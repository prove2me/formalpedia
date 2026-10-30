-- Prove2me | Theorems.Thm_BitcoinMuSig_pmul_add
-- name    : BitcoinMuSig.pmul_add
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:31:18.794652+00:00
-- url     : https://prove2.me/theorems/dfef89ea-0e6b-4f83-b830-75cf42555246
-- title:
--   The scalar ladder is additive in the scalar
-- statement:
--   `pmul (a+b) P = padd (pmul a P) (pmul b P)` for $a + b < 2^{257}$ and valid, reduced $P$.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.pmul_add (a b : ℕ) (P : Point) (hP : Valid P) (hPr : Reduced P)
    (hab : a + b < 2 ^ 257) :
    pmul (a + b) P = padd (pmul a P) (pmul b P) := by sorry
