-- Prove2me | Theorems.Thm_BitcoinMuSig_frost_correct
-- name    : BitcoinMuSig.frost_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:40:19.100386+00:00
-- url     : https://prove2.me/theorems/0d65ecc7-5933-4013-8bc0-fd2cee42cb9f
-- title:
--   FROST correctness with Shamir shares
-- statement:
--   In a `ZMod n`-module, with shares $f(i)$ of a polynomial of degree below $|S|$: $(\sum z_i)G = R + c\,(f(0)G)$, the Schnorr equation for the group key $f(0)G$.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.frost_correct {M : Type*} [AddCommGroup M] [Module (ZMod n) M] (G : M)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < n) (f : Polynomial (ZMod n)) (hdeg : f.degree < S.card)
    (D E : ℕ → M) (ρ z : ℕ → ZMod n) (c : ZMod n)
    (hz : ∀ i ∈ S, z i • G = D i + ρ i • E i + (c * lagrangeCoeff S i) • (f.eval (i : ZMod n) • G)) :
    (∑ i ∈ S, z i) • G = ∑ i ∈ S, (D i + ρ i • E i) + c • (f.eval 0 • G) := by sorry
