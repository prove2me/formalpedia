-- Prove2me | Theorems.Thm_BitcoinMuSig_n_nsmul_Gpt
-- name    : BitcoinMuSig.n_nsmul_Gpt
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:33:26.080526+00:00
-- url     : https://prove2.me/theorems/7448c7a5-0de4-4435-bcb5-1eb18f28b356
-- title:
--   The generator has order dividing n
-- statement:
--   `n • Gpt = 0`, by kernel evaluation of `pmul n G = none`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.n_nsmul_Gpt : n • Gpt = 0 := by sorry
