-- Prove2me | Theorems.Thm_BitcoinMuSig_lagrange_interpolate_zero
-- name    : BitcoinMuSig.lagrange_interpolate_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:38:53.040573+00:00
-- url     : https://prove2.me/theorems/a5a155ca-2390-46a8-afed-1f6458c97dd4
-- title:
--   Lagrange interpolation at 0
-- statement:
--   For identifiers below $n$ and a polynomial of degree below $|S|$ over `ZMod n`: $\sum_{i\in S} \lambda_i f(i) = f(0)$.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.lagrange_interpolate_zero (S : Finset ℕ) (hS : ∀ i ∈ S, i < n)
    (f : Polynomial (ZMod n)) (hdeg : f.degree < S.card) :
    ∑ i ∈ S, lagrangeCoeff S i * f.eval (i : ZMod n) = f.eval 0 := by sorry
