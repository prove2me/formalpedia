-- Prove2me | Theorems.Thm_BitcoinMuSig_pmul_padd
-- name    : BitcoinMuSig.pmul_padd
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:31:45.697683+00:00
-- url     : https://prove2.me/theorems/cfe82e72-d933-4562-b28e-920a42fa599a
-- title:
--   The scalar ladder distributes over addition
-- statement:
--   `pmul k (padd P Q) = padd (pmul k P) (pmul k Q)`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.pmul_padd (k : ℕ) (P Q : Point) (hP : Valid P) (hQ : Valid Q) (hPr : Reduced P)
    (hQr : Reduced Q) (hk : k < 2 ^ 257) :
    pmul k (padd P Q) = padd (pmul k P) (pmul k Q) := by sorry
