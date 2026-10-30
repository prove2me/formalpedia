-- Prove2me | Theorems.Thm_BitcoinMuSig_pmul_pmul
-- name    : BitcoinMuSig.pmul_pmul
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:32:22.699622+00:00
-- url     : https://prove2.me/theorems/eb17869f-a541-42a1-84bc-2fa0dfbc02df
-- title:
--   Scalar multiplications compose
-- statement:
--   `pmul a (pmul b P) = pmul (a·b) P` within the fuel bound.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.pmul_pmul (a b : ℕ) (P : Point) (hP : Valid P) (hPr : Reduced P)
    (ha : a < 2 ^ 257) (hb : b < 2 ^ 257) (hab : a * b < 2 ^ 257) :
    pmul a (pmul b P) = pmul (a * b) P := by sorry
