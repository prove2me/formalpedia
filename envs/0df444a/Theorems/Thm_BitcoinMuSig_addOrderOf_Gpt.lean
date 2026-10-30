-- Prove2me | Theorems.Thm_BitcoinMuSig_addOrderOf_Gpt
-- name    : BitcoinMuSig.addOrderOf_Gpt
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:34:42.010869+00:00
-- url     : https://prove2.me/theorems/eb591de6-fce7-47f2-ae49-8d5df5886779
-- title:
--   The generator has order exactly n
-- statement:
--   `addOrderOf Gpt = n`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.addOrderOf_Gpt : addOrderOf Gpt = n := by sorry
