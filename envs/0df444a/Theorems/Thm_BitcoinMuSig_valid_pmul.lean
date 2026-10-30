-- Prove2me | Theorems.Thm_BitcoinMuSig_valid_pmul
-- name    : BitcoinMuSig.valid_pmul
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:28:02.090155+00:00
-- url     : https://prove2.me/theorems/ade69953-1c6a-4589-a3e0-e6b31bdfcc6a
-- title:
--   Scalar multiples of curve points are on the curve
-- statement:
--   For $k < 2^{257}$ (the ladder's fuel): `Valid (pmul k P)`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.valid_pmul (k : ℕ) (P : Point) (hP : Valid P) (hk : k < 2 ^ 257) :
    Valid (pmul k P) := by sorry
