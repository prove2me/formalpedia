-- Prove2me | Theorems.Thm_BitcoinMuSig_frost_correct_secp256k1
-- name    : BitcoinMuSig.frost_correct_secp256k1
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:40:49.028377+00:00
-- url     : https://prove2.me/theorems/b9e3e8a9-79a3-43c6-8db5-bcf9d3cf3012
-- title:
--   FROST correctness on secp256k1
-- statement:
--   `frost_correct` on Mathlib's points of $W$ with `ZMod n` scalars acting through their representatives.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.frost_correct_secp256k1 (S : Finset ℕ) (hS : ∀ i ∈ S, i < n)
    (f : Polynomial (ZMod n)) (hdeg : f.degree < S.card) (D E : ℕ → W.Point) (ρ z : ℕ → ZMod n)
    (c : ZMod n)
    (hz : ∀ i ∈ S, (z i).val • Gpt =
      D i + (ρ i).val • E i + (c * lagrangeCoeff S i).val • ((f.eval (i : ZMod n)).val • Gpt)) :
    (∑ i ∈ S, z i).val • Gpt = ∑ i ∈ S, (D i + (ρ i).val • E i) + c.val • ((f.eval 0).val • Gpt) := by sorry
