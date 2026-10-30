-- Prove2me | Theorems.Thm_BitcoinMuSig_toPoint_pneg
-- name    : BitcoinMuSig.toPoint_pneg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:29:15.055313+00:00
-- url     : https://prove2.me/theorems/4027a5c6-eac7-4c47-8eb0-4906ca8d846c
-- title:
--   The executable negation is Mathlib's negation
-- statement:
--   `toPoint (pneg P) = some (-tp P)` for valid $P$.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.toPoint_pneg (P : Point) (hP : Valid P) : toPoint (pneg P) = some (-tp P) := by sorry
