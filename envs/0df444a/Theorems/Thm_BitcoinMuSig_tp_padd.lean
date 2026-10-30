-- Prove2me | Theorems.Thm_BitcoinMuSig_tp_padd
-- name    : BitcoinMuSig.tp_padd
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:27:29.131576+00:00
-- url     : https://prove2.me/theorems/f6126a0a-68f8-4afb-81c9-e827ac9f1570
-- title:
--   tp is additive
-- statement:
--   For valid points: `tp (padd P Q) = tp P + tp Q`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.tp_padd (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    tp (padd P Q) = tp P + tp Q := by sorry
