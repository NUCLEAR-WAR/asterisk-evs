/*** MODULEINFO
	<depend>evs</depend>
***/

#include "asterisk.h"

#include <math.h>                       /* for log10, floor */

#include "asterisk/astobj2.h"           /* for ao2_ref */
#include "asterisk/codec.h"             /* for AST_MEDIA_TYPE_AUDIO */
#include "asterisk/frame.h"             /* for ast_frame, etc */
#include "asterisk/linkedlists.h"       /* for AST_LIST_NEXT, etc */
#include "asterisk/logger.h"            /* for ast_log, ast_debug, etc */
#include "asterisk/module.h"
#include "asterisk/rtp_engine.h"       /* for ast_rtp_engine_load_format */
#include "asterisk/translate.h"         /* for ast_trans_pvt, etc */

#include "asterisk/evs.h"               /* for evs_attr */

#undef NO_DATA                          /* already defined in <netdb.h> */
#include <3gpp-evs/cnst.h>              /* for MAX_BITS_PER_FRAME, etc */
#include <3gpp-evs/prot.h>              /* for amr_wb_enc, etc */
#include <3gpp-evs/stat_com.h>          /* for FRAMEMODE_NORMAL */
#include <3gpp-evs/typedef.h>           /* for UWord8, UWord16, Word16 */
#include <3gpp-evs/mime.h>              /* for AMRWB_IOmode2rate, etc */
/* mime.h must come last because typedef.h (Word16, Word32) missing */

#define BUFFER_SAMPLES 28800 /* 15 EVS frames at 48 kHz, in bytes */
#define BUFFER_BYTES   (MAX_BITS_PER_FRAME + 7) / 8
#define	EVS_SAMPLES    320
#define EVS_MAX_FRAMES 15

/* Sample frame data */
#include "asterisk/slin.h"
#include "ex_evs.h"

/*
 * Stores the function pointer 'sample_count' of the cached ast_codec
 * before this module was loaded. Allows to restore this previous
 * function pointer, when this module in unloaded.
 */
static struct ast_codec *evs_codec; /* codec of the cached format */
static int (*evs_previous_sample_counter)(struct ast_frame *frame);
static unsigned int evs_previous_maximum_ms;

struct evs_coder_pvt {
	Encoder_State *encoder;
	Decoder_State *decoder;
	short buf[BUFFER_SAMPLES];
	float con[BUFFER_BYTES];
	Indice ind_list[MAX_NUM_INDICES];
};

static Word16 rate2AMRWB_IOmode(Word32 rate);
static Word16 rate2EVSmode(Word32 rate);
static short select_mode(short Opt_AMR_WB, short Opt_RF_ON, long total_brate);
static int select_bit_rate(int bit_rate, int max_bandwidth);

static Word16 rate2AMRWB_IOmode(Word32 rate)
{
	switch (rate) {
	/* EVS AMR-WB IO modes */
	case SID_1k75:
		return AMRWB_IO_SID;
	case ACELP_6k60:
		return AMRWB_IO_6600;
	case ACELP_8k85:
		return AMRWB_IO_8850;
	case ACELP_12k65:
		return AMRWB_IO_1265;
	case ACELP_14k25:
		return AMRWB_IO_1425;
	case ACELP_15k85:
		return AMRWB_IO_1585;
	case ACELP_18k25:
		return AMRWB_IO_1825;
	case ACELP_19k85:
		return AMRWB_IO_1985;
	case ACELP_23k05:
		return AMRWB_IO_2305;
	case ACELP_23k85:
		return AMRWB_IO_2385;
	default:
		return -1;
	}
}

static Word16 rate2EVSmode(Word32 rate)
{
	switch (rate) {
	/* EVS Primary modes */
	case FRAME_NO_DATA :
		return NO_DATA;
	case SID_2k40:
		return PRIMARY_SID;
	case PPP_NELP_2k80:
		return PRIMARY_2800;
	case ACELP_7k20:
		return PRIMARY_7200;
	case ACELP_8k00:
		return PRIMARY_8000;
	case ACELP_9k60:
		return PRIMARY_9600;
	case ACELP_13k20:
		return PRIMARY_13200;
	case ACELP_16k40:
		return PRIMARY_16400;
	case ACELP_24k40:
		return PRIMARY_24400;
	case ACELP_32k:
		return PRIMARY_32000;
	case ACELP_48k:
		return PRIMARY_48000;
	case ACELP_64k:
		return PRIMARY_64000;
	case HQ_96k:
		return PRIMARY_96000;
	case HQ_128k:
		return PRIMARY_128000;
	default:
		return rate2AMRWB_IOmode(rate);
	}
}

/* Copy & Paste from lib_enc/io_enc.c:io_ini_enc */
static short select_mode(short Opt_AMR_WB, short Opt_RF_ON, long total_brate)
{
	if (Opt_AMR_WB) {
		return MODE1;
	}

	switch (total_brate) {
	case 2800:
		return MODE1;
	case 7200:
		return MODE1;
	case 8000:
		return MODE1;
	case 9600:
		return MODE2;
	case 13200:
		if (Opt_RF_ON) {
			return MODE2;
		} else {
			return MODE1;
		}
	case 16400:
		return MODE2;
	case 24400:
		return MODE2;
	case 32000:
		return MODE1;
	case 48000:
		return MODE2;
	case 64000:
		return MODE1;
	case 96000:
		return MODE2;
	case 128000:
		return MODE2;
	}

	ast_log(LOG_ERROR, "unexpected bit-rate %ld\n", total_brate);
	return 0;
}

static int select_bit_rate(int bit_rate, int max_bandwidth)
{
	switch (max_bandwidth) {
	case NB:
		return MIN(bit_rate, PRIMARY_24400);
	default:
		return bit_rate;
	}
}

static int lintoevs_new(struct ast_trans_pvt *pvt)
{
	struct evs_coder_pvt *apvt = pvt->pvt;
	const unsigned int sample_rate = pvt->t->src_codec.sample_rate;

	struct evs_attr *attr = pvt->explicit_dst ?
		ast_format_get_attribute_data(pvt->explicit_dst) : NULL;
	const int channel_aware = attr ? MIN(attr->ch_aw_send, attr->ch_aw_recv) : -2;
	const unsigned int dtx_on = attr ? MIN(attr->dtx, attr->dtx_send) : 0;
	const int amr_wb = attr ? attr->evs_mode_switch : -1;
	const int max_bandwidth = attr ? /* WB matches all bit-rates */
		floor(log10(attr->bw_send) / log10(2)) - 1 : WB;
	int bit_rate_evs = attr ? /* 16.4 is available in all bandwidths */
		floor(log10(attr->br_send) / log10(2)) - 1 : PRIMARY_16400;
	int bit_rate_amr;

	apvt->encoder = ast_malloc(sizeof(*apvt->encoder));
	if (NULL == apvt->encoder) {
		ast_log(LOG_ERROR, "Error creating the 3GPP EVS encoder\n");
		return -1;
	}

	if (attr && 0 < attr->mode_set) {
		bit_rate_amr = floor(log10(attr->mode_set) / log10(2));
	} else {
		bit_rate_amr = AMRWB_IO_2385;
	}

	apvt->encoder->ind_list = apvt->ind_list;
	apvt->encoder->input_Fs = sample_rate;
	/* Value range:  0..2, see res/res_format_attr_evs.c */
	apvt->encoder->Opt_DTX_ON = (0 < dtx_on);
	apvt->encoder->var_SID_rate_flag = 1; /* Automatic interval */
	/* Value range: -1..1, see res/res_format_attr_evs.c */
	apvt->encoder->Opt_AMR_WB = (0 < amr_wb);
	/* Value range: -2..7, see res/res_format_attr_evs.c */
	apvt->encoder->Opt_RF_ON = (0 < channel_aware);
	if (apvt->encoder->Opt_RF_ON) {
		/* EVS library crashed with higher values */
		apvt->encoder->rf_fec_offset = MIN(channel_aware, MAX_RF_FEC_OFFSET);
	} else {
		/* Must be set although it should follow Opt_RF_ON */
		apvt->encoder->rf_fec_offset = 0;
	}
	apvt->encoder->rf_fec_indicator = 1; /* Frame-erasure-rate indicator = HI */

	/* Variable bit-rate (SC-VBR) requires DTX according to the 3GPP EVS
	 * library "lib_enc/io_enc.c:io_ini_enc" cases:
	 * 1) st->Opt_SC_VBR && !st->Opt_DTX_ON
	 * 2) st->total_brate == ACELP_5k90 */
	apvt->encoder->Opt_SC_VBR = (0 == bit_rate_evs);
	if (sample_rate <= 8000 || max_bandwidth == NB) {
		apvt->encoder->max_bwidth = NB;
	} else if (sample_rate <= 16000 || max_bandwidth == WB || apvt->encoder->Opt_SC_VBR) {
		apvt->encoder->max_bwidth = WB;
	} else if (sample_rate <= 32000 || max_bandwidth == SWB) {
		apvt->encoder->max_bwidth = SWB;
	} else {
		apvt->encoder->max_bwidth = FB;
	}
	if (apvt->encoder->Opt_AMR_WB) {
		apvt->encoder->total_brate = AMRWB_IOmode2rate[bit_rate_amr];
	} else if (apvt->encoder->Opt_SC_VBR) {
		apvt->encoder->total_brate = PRIMARYmode2rate[PRIMARY_7200];
	} else {
		bit_rate_evs = select_bit_rate(bit_rate_evs, apvt->encoder->max_bwidth);
		apvt->encoder->total_brate = PRIMARYmode2rate[bit_rate_evs];
	}
	apvt->encoder->codec_mode = select_mode(apvt->encoder->Opt_AMR_WB,
		apvt->encoder->Opt_RF_ON, apvt->encoder->total_brate);
	apvt->encoder->last_codec_mode = apvt->encoder->codec_mode;

	/* After setting the above parameters (some set other parameters) */
	init_encoder(apvt->encoder);

	if (attr) {
		if (apvt->encoder->Opt_AMR_WB) {
			attr->mode_current = 0x10 + bit_rate_amr;
		} else if (apvt->encoder->max_bwidth ==  NB) {
			attr->mode_current = 0x00 + bit_rate_evs;
		} else if (apvt->encoder->max_bwidth ==  WB) {
			attr->mode_current = 0x20 + bit_rate_evs;
		} else if (apvt->encoder->max_bwidth == SWB) {
			attr->mode_current = 0x30 + bit_rate_evs;
		} else { /* FB */
			attr->mode_current = 0x40 + bit_rate_evs;
		}
	}

	ast_debug(3, "Created encoder (3GPP EVS) with sample rate %d\n", sample_rate);
	return 0;
}

static int evstolin_new(struct ast_trans_pvt *pvt)
{
	struct evs_coder_pvt *apvt = pvt->pvt;
	const unsigned int sample_rate = pvt->t->dst_codec.sample_rate;

	apvt->decoder = ast_malloc(sizeof(*apvt->decoder));
	if (NULL == apvt->decoder) {
		ast_log(LOG_ERROR, "Error creating the 3GPP EVS decoder\n");
		return -1;
	}

	apvt->decoder->output_Fs = sample_rate;
	init_decoder(apvt->decoder);

	ast_debug(3, "Created decoder (3GPP EVS) with sample rate %d\n", sample_rate);
	return 0;
}

static int lintoevs_framein(struct ast_trans_pvt *pvt, struct ast_frame *f)
{
	struct evs_coder_pvt *apvt = pvt->pvt;

	/* XXX We should look at how old the rest of our stream is, and if it
	 is too old, then we should overwrite it entirely, otherwise we can
	 get artifacts of earlier talk that do not belong */
	if (pvt->samples > BUFFER_SAMPLES / 2 ||
	    f->datalen > sizeof(apvt->buf) - pvt->samples * sizeof(apvt->buf[0])) {
		ast_log(LOG_WARNING, "EVS encoder input exceeds buffer\n");
		return -1;
	}
	memcpy(apvt->buf + pvt->samples, f->data.ptr, f->datalen);
	pvt->samples += f->samples;

	return 0;
}

static struct ast_frame *lintoevs_frameout(struct ast_trans_pvt *pvt)
{
	struct evs_coder_pvt *apvt = pvt->pvt;
	const unsigned int sample_rate = pvt->t->src_codec.sample_rate;
	const unsigned int max_bandwidth = ((sample_rate / 8000) >> 1);
	const short n_samples = sample_rate / 50;
	struct ast_frame *result = NULL;
	struct ast_frame *last = NULL;
	int samples = 0; /* Output samples */

	struct evs_attr *attr = ast_format_get_attribute_data(pvt->f.subclass.format);
	const int mode = attr ? attr->mode_current :
		((0x20 >> apvt->encoder->Opt_AMR_WB) + PRIMARY_16400); /* 0x20 is WB */
	const int cmr = attr ? attr->cmr : 0;
	const int bandwidth = (mode & 0x70);
	unsigned int bit_rate = (mode & 0x0f);

	if (0x10 == bandwidth) {
		apvt->encoder->Opt_AMR_WB = 1;
		apvt->encoder->total_brate = AMRWB_IOmode2rate[bit_rate];
	} else if (mode <= 0x7f) { /* 0xff = NO_REQ */
		apvt->encoder->Opt_AMR_WB = 0;
		apvt->encoder->total_brate = PRIMARYmode2rate[bit_rate];
		apvt->encoder->Opt_SC_VBR = 0;
		apvt->encoder->Opt_RF_ON = 0;
		if (0x00 == bandwidth) {
			apvt->encoder->max_bwidth = MIN(max_bandwidth,  NB);
			if (0 == bit_rate) {
				apvt->encoder->Opt_SC_VBR = 1;
				apvt->encoder->total_brate = PRIMARYmode2rate[PRIMARY_7200];
			}
		} else if (0x20 == bandwidth) {
			apvt->encoder->max_bwidth = MIN(max_bandwidth,  WB);
			if (0 == bit_rate) {
				apvt->encoder->Opt_SC_VBR = 1;
				apvt->encoder->total_brate = PRIMARYmode2rate[PRIMARY_7200];
			}
		} else if (0x30 == bandwidth) {
			apvt->encoder->max_bwidth = MIN(max_bandwidth, SWB);
		} else if (0x40 == bandwidth) {
			apvt->encoder->max_bwidth = MIN(max_bandwidth,  FB);
		} else if (0x50 == bandwidth) {
			apvt->encoder->Opt_RF_ON = 1;
			apvt->encoder->total_brate = PRIMARYmode2rate[PRIMARY_13200];
			apvt->encoder->max_bwidth = MIN(max_bandwidth,  WB);
		} else if (0x60 == bandwidth) {
			apvt->encoder->Opt_RF_ON = 1;
			apvt->encoder->total_brate = PRIMARYmode2rate[PRIMARY_13200];
			apvt->encoder->max_bwidth = MIN(max_bandwidth, SWB);
		} /* else (0x70) is reserved; do nothing */
	}
	apvt->encoder->codec_mode = select_mode(apvt->encoder->Opt_AMR_WB,
		apvt->encoder->Opt_RF_ON, apvt->encoder->total_brate);

	while (pvt->samples >= n_samples) {
		struct ast_frame *current;
		unsigned char *out = pvt->outbuf.uc;
		const short *in = apvt->buf + samples;
		int datalen = 0;

		if (apvt->encoder->Opt_AMR_WB) {
			amr_wb_enc(apvt->encoder, in, n_samples);
		} else {
			evs_enc(apvt->encoder, in, n_samples);
		}

		samples += n_samples;
		pvt->samples -= n_samples;

		bit_rate = rate2EVSmode(apvt->encoder->nb_bits_tot * 50);
		if (bit_rate == NO_DATA) {
			continue; /* happens in case of DTX */
		} else if (bit_rate < 0) {
			ast_log(LOG_ERROR, "Error encoding the 3GPP EVS frame (code: %d)\n", apvt->encoder->nb_bits_tot);
			continue;
		}

		/* Change Mode Request (CMR) */
		if (apvt->encoder->Opt_AMR_WB || 1 == cmr) {
			out[0] = 0x7f; /* NO_REQ = no change in mode requested */
			out[0] = out[0] | 0x80; /* Header Type identification bit */
			datalen = datalen + 1;
			out++;
		}

		/* Table of Content (ToC), see lib_com/bitstream.c:write_indices */
		out[0] = 0x00; /* Header Type identification and Followed bit */
		out[0] |= (apvt->encoder->Opt_AMR_WB << 5); /* EVS mode bit */
		out[0] |= (apvt->encoder->Opt_AMR_WB << 4); /* Quality bit */
		out[0] |= bit_rate;
		datalen = datalen + 1;
		out++;

		/* Payload: fill rest of buffer, which is going to be send via RTP */
		indices_to_serial(apvt->encoder, out, &apvt->encoder->nb_bits_tot);

		/* Convert bits into bytes, +7 is for rounding-up */
		datalen = datalen + ((apvt->encoder->nb_bits_tot + 7) / 8);
		/* out was and is still part of pvt->outbuf.uc */
		current = ast_trans_frameout(pvt, datalen, EVS_SAMPLES);

		/* Everything used, therefore reset hidden index pointers */
		reset_indices_enc(apvt->encoder);

		if (!current) {
			continue;
		} else if (last) {
			AST_LIST_NEXT(last, frame_list) = current;
		} else {
			result = current;
		}
		last = current;
	}

	/* Move the data at the end of the buffer to the front */
	if (samples) {
		memmove(apvt->buf, apvt->buf + samples, pvt->samples * 2);
	}

	return result;
}

/* Header-Full ToCs precede all speech payloads. Validate the complete packet
 * before allowing the reference decoder to inspect any of its bits. */
static int evs_parse_packet(const unsigned char *data, size_t length,
    unsigned int rates[EVS_MAX_FRAMES], unsigned char modes[EVS_MAX_FRAMES],
    unsigned char qbits[EVS_MAX_FRAMES], const unsigned char **payload,
    unsigned int *count, int *cmr)
{
    size_t pos = 0, bytes = 0;
    unsigned int n = 0;
    unsigned char toc;

    if (!length) {
        return -1;
    }
    *cmr = -1;
    if (data[0] & 0x80) {
        /* H=1 identifies the optional CMR. 0xff means NO_REQ. */
        *cmr = data[0] & 0x7f;
        pos++;
    }
    do {
        unsigned int rate, mode;
        if (pos >= length || n == EVS_MAX_FRAMES) {
            return -1;
        }
        toc = data[pos++];
        if (toc & 0x80) {
            return -1;
        }
        mode = toc & 0x0f;
        if (toc & 0x20) {
            rate = AMRWB_IOmode2rate[mode];
        } else {
            if (toc & 0x10) { /* unused bit in primary-mode ToC */
                return -1;
            }
            rate = PRIMARYmode2rate[mode];
        }
        if ((int)rate < 0 || rate / 50 > MAX_BITS_PER_FRAME) {
            return -1;
        }
        modes[n] = toc;
        rates[n] = rate;
        qbits[n] = (toc & 0x20) ? !!(toc & 0x10) : 1;
		/* AMR-WB SID appends STI and four CMI bits in the same byte stream. */
		bytes += (rate / 50 + ((toc & 0x20) && rate == SID_1k75 ? 5 : 0) + 7) / 8;
        n++;
    } while (toc & 0x40);
    if (bytes != length - pos) {
        return -1;
    }
    *payload = data + pos;
    *count = n;
    return 0;
}

static int evstolin_framein(struct ast_trans_pvt *pvt, struct ast_frame *f)
{
    struct evs_coder_pvt *apvt = pvt->pvt;
    struct evs_attr *attr = ast_format_get_attribute_data(f->subclass.format);
    const unsigned int n_samples = pvt->t->dst_codec.sample_rate / 50;
    unsigned int rates[EVS_MAX_FRAMES], count, i;
    unsigned char modes[EVS_MAX_FRAMES], qbits[EVS_MAX_FRAMES];
    const unsigned char *payload;
    int cmr;

	if (evs_parse_packet(f->data.ptr, f->datalen, rates, modes, qbits,
	        &payload, &count, &cmr) ||
	    pvt->samples > BUFFER_SAMPLES / 2 ||
	    count * n_samples > (BUFFER_SAMPLES / 2) - pvt->samples) {
        ast_log(LOG_WARNING, "Invalid or oversized EVS Header-Full packet\n");
        return -1;
    }
    if (attr && cmr >= 0 && cmr != 0x7f) {
        attr->mode_current = cmr;
    }
    /* The ETSI routine reorders AMR-WB IO bits when reading RTP payloads. */
    apvt->decoder->bitstreamformat = VOIP_RTPDUMP;
    for (i = 0; i < count; i++) {
        unsigned int bits = rates[i] / 50;
		unsigned int bytes = (bits + ((modes[i] & 0x20) &&
		    rates[i] == SID_1k75 ? 5 : 0) + 7) / 8;
        unsigned int amr = !!(modes[i] & 0x20);
        unsigned int mode = modes[i] & 0x0f;
        apvt->decoder->Opt_AMR_WB = amr;
        read_indices_from_djb(apvt->decoder, (unsigned char *)payload, bits,
            amr, mode, qbits[i], 0, 0);
        if (amr) {
            amr_wb_dec(apvt->decoder, apvt->con);
        } else {
            evs_dec(apvt->decoder, apvt->con, FRAMEMODE_NORMAL);
        }
        syn_output(apvt->con, n_samples, pvt->outbuf.i16 + pvt->samples);
        if (apvt->decoder->ini_frame < MAX_FRAME_COUNTER) {
            apvt->decoder->ini_frame++;
        }
        pvt->samples += n_samples;
        pvt->datalen += n_samples * sizeof(short);
		payload += bytes;
    }
    return 0;
}

static void lintoevs_destroy(struct ast_trans_pvt *pvt)
{
	struct evs_coder_pvt *apvt = pvt->pvt;

	if (NULL == apvt || NULL == apvt->encoder) {
		return;
	}

	destroy_encoder(apvt->encoder);
	ast_free(apvt->encoder);

	ast_debug(3, "Destroyed encoder (3GPP EVS)\n");
}

static void evstolin_destroy(struct ast_trans_pvt *pvt)
{
	struct evs_coder_pvt *apvt = pvt->pvt;

	if (NULL == apvt || NULL == apvt->decoder) {
		return;
	}

	destroy_decoder(apvt->decoder);
	ast_free(apvt->decoder);

	ast_debug(3, "Destroyed decoder (3GPP EVS)\n");
}

static struct ast_translator evstolin = {
	.table_cost = AST_TRANS_COST_LY_LL_ORIGSAMP,
	.name = "evstolin",
	.src_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.dst_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 8000,
	},
	.format = "slin",
	.newpvt = evstolin_new,
	.framein = evstolin_framein,
	.destroy = evstolin_destroy,
	.sample = evs_sample,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator lintoevs = {
	.table_cost = AST_TRANS_COST_LL_LY_ORIGSAMP,
	.name = "lintoevs",
	.src_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 8000,
	},
	.dst_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.format = "evs",
	.newpvt = lintoevs_new,
	.framein = lintoevs_framein,
	.frameout = lintoevs_frameout,
	.destroy = lintoevs_destroy,
	.sample = slin8_sample,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator evstolin16 = {
	.table_cost = AST_TRANS_COST_LY_LL_ORIGSAMP - 1,
	.name = "evstolin16",
	.src_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.dst_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.format = "slin16",
	.newpvt = evstolin_new,
	.framein = evstolin_framein,
	.destroy = evstolin_destroy,
	.sample = evs_sample,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator lin16toevs = {
	.table_cost = AST_TRANS_COST_LL_LY_ORIGSAMP - 1,
	.name = "lin16toevs",
	.src_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.dst_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.format = "evs",
	.newpvt = lintoevs_new,
	.framein = lintoevs_framein,
	.frameout = lintoevs_frameout,
	.destroy = lintoevs_destroy,
	.sample = slin16_sample,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator evstolin32 = {
	.table_cost = AST_TRANS_COST_LY_LL_ORIGSAMP - 2,
	.name = "evstolin32",
	.src_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.dst_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 32000,
	},
	.format = "slin32",
	.newpvt = evstolin_new,
	.framein = evstolin_framein,
	.destroy = evstolin_destroy,
	.sample = evs_sample,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator lin32toevs = {
	.table_cost = AST_TRANS_COST_LL_LY_ORIGSAMP - 2,
	.name = "lin32toevs",
	.src_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 32000,
	},
	.dst_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.format = "evs",
	.newpvt = lintoevs_new,
	.framein = lintoevs_framein,
	.frameout = lintoevs_frameout,
	.destroy = lintoevs_destroy,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator evstolin48 = {
	.table_cost = AST_TRANS_COST_LY_LL_ORIGSAMP - 4,
	.name = "evstolin48",
	.src_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.dst_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 48000,
	},
	.format = "slin48",
	.newpvt = evstolin_new,
	.framein = evstolin_framein,
	.destroy = evstolin_destroy,
	.sample = evs_sample,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static struct ast_translator lin48toevs = {
	.table_cost = AST_TRANS_COST_LL_LY_ORIGSAMP - 4,
	.name = "lin48toevs",
	.src_codec = {
		.name = "slin",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 48000,
	},
	.dst_codec = {
		.name = "evs",
		.type = AST_MEDIA_TYPE_AUDIO,
		.sample_rate = 16000,
	},
	.format = "evs",
	.newpvt = lintoevs_new,
	.framein = lintoevs_framein,
	.frameout = lintoevs_frameout,
	.destroy = lintoevs_destroy,
	.desc_size = sizeof(struct evs_coder_pvt),
	.buffer_samples = BUFFER_SAMPLES / 2,
	.buf_size = BUFFER_SAMPLES,
};

static int evs_sample_counter(struct ast_frame *frame)
{
    unsigned int rates[EVS_MAX_FRAMES], count;
    unsigned char modes[EVS_MAX_FRAMES], qbits[EVS_MAX_FRAMES];
    const unsigned char *payload;
    int cmr;

    if (evs_parse_packet(frame->data.ptr, frame->datalen, rates, modes,
            qbits, &payload, &count, &cmr)) {
        return 0;
    }
    return count * EVS_SAMPLES;
}

static int unload_module(void)
{
	int res;

	if (evs_codec) {
		evs_codec->samples_count = evs_previous_sample_counter;
		evs_codec->maximum_ms = evs_previous_maximum_ms;
		ao2_ref(evs_codec, -1);
	}

	res = ast_unregister_translator(&evstolin);
	res |= ast_unregister_translator(&lintoevs);
	res |= ast_unregister_translator(&evstolin16);
	res |= ast_unregister_translator(&lin16toevs);
	res |= ast_unregister_translator(&evstolin32);
	res |= ast_unregister_translator(&lin32toevs);
	res |= ast_unregister_translator(&evstolin48);
	res |= ast_unregister_translator(&lin48toevs);

	return res;
}

static int load_module(void)
{
	int res;

	evs_codec = ast_codec_get("evs", AST_MEDIA_TYPE_AUDIO, 16000);
	if (NULL == evs_codec) {
		ast_log(LOG_ERROR, "Please, apply the file 'codec_evs.patch'!\n");
		return AST_MODULE_LOAD_DECLINE;
	}
	evs_previous_sample_counter = evs_codec->samples_count;
	evs_codec->samples_count = evs_sample_counter;
	evs_previous_maximum_ms = evs_codec->maximum_ms;
	evs_codec->maximum_ms = 300; /* 15 Header-Full frames */
	/* A smoothable codec allows Asterisk to put several frame blocks
	 * into one RTP packet, for example when the negotiated paketization
	 * time (ptime) is 60ms. Frames of codecs like 3GPP EVS cannot be put
	 * like this into a RTP packet, because each frame block might have a
	 * different length. Therefore, 3GPP EVS works with a Table of Contents.
	 * Or stated differently: Smoothable works only with codecs which have
	 * known fixed size, the same for each frame block. Commented because it
	 * is set already, being non-smoothable is the default. */
	/* evs_codec->smooth = 0; */

	res = ast_register_translator(&evstolin);
	res |= ast_register_translator(&lintoevs);
	res |= ast_register_translator(&evstolin16);
	res |= ast_register_translator(&lin16toevs);
	res |= ast_register_translator(&evstolin32);
	res |= ast_register_translator(&lin32toevs);
	res |= ast_register_translator(&evstolin48);
	res |= ast_register_translator(&lin48toevs);
  res |= ast_rtp_engine_load_format(ast_format_evs);
	if (res) {
		unload_module();
		return AST_MODULE_LOAD_DECLINE;
	}

	return AST_MODULE_LOAD_SUCCESS;
}

AST_MODULE_INFO_STANDARD(ASTERISK_GPL_KEY, "3GPP EVS Coder/Decoder");
