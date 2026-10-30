-- Prove2me | Theorems.Thm_BitcoinMuSig_musig2_partialSigAgg_secp256k1
-- name    : BitcoinMuSig.musig2_partialSigAgg_secp256k1
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:38:00.919553+00:00
-- url     : https://prove2.me/theorems/0380bd89-7bd7-44c9-9d75-4932489d497c
-- title:
--   MuSig2 aggregation on secp256k1's group
-- statement:
--   `musig2_partialSigAgg` on Mathlib's points of $W$ with generator `Gpt` and integer scalars.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_partialSigAgg_secp256k1 {ι : Type*} (S : Finset ι) (X R₁ R₂ : ι → W.Point)
    (a s : ι → ℤ) (b e g gacc tacc ε : ℤ) (Q : W.Point)
    (hQ : Q = gacc • ∑ i ∈ S, a i • X i + tacc • Gpt)
    (hpart : ∀ i ∈ S, s i • Gpt = ε • (R₁ i + b • R₂ i) + (e * a i * (g * gacc)) • X i) :
    (∑ i ∈ S, s i + e * g * tacc) • Gpt = ε • (∑ i ∈ S, R₁ i + b • ∑ i ∈ S, R₂ i) + e • (g • Q) := by sorry
