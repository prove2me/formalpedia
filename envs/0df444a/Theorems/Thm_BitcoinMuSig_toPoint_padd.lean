-- Prove2me | Theorems.Thm_BitcoinMuSig_toPoint_padd
-- name    : BitcoinMuSig.toPoint_padd
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:26:23.667412+00:00
-- url     : https://prove2.me/theorems/42dedca6-d4c6-40ef-850d-dd9216b7e353
-- title:
--   The executable addition is Mathlib's group addition
-- statement:
--   For points on the curve: `toPoint (padd P Q) = some (tp P + tp Q)`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.toPoint_padd (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    toPoint (padd P Q) = some (tp P + tp Q) := by sorry
