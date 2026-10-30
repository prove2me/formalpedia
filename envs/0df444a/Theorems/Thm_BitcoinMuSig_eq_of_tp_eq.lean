-- Prove2me | Theorems.Thm_BitcoinMuSig_eq_of_tp_eq
-- name    : BitcoinMuSig.eq_of_tp_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:29:50.847966+00:00
-- url     : https://prove2.me/theorems/542ebbdf-638b-4b4b-8619-810872777e3b
-- title:
--   tp is injective on reduced curve points
-- statement:
--   Valid, reduced $P$, $Q$ with `tp P = tp Q` are equal.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.eq_of_tp_eq (P Q : Point) (hP : Valid P) (hQ : Valid Q) (hPr : Reduced P)
    (hQr : Reduced Q) (h : tp P = tp Q) : P = Q := by sorry
