-- Prove2me | Theorems.Thm_BitcoinMuSig_musig2_correct
-- name    : BitcoinMuSig.musig2_correct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:37:34.826375+00:00
-- url     : https://prove2.me/theorems/c68a8233-1ade-4c64-b1f8-d9d9917ddb5d
-- title:
--   MuSig2 correctness with honest signers
-- statement:
--   Honest partial signatures sum to a signature satisfying the Schnorr equation for the aggregate key.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_correct {ι K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (S : Finset ι) (G : M) (d k₁ k₂ a : ι → K) (b e g gacc tacc ε : K) :
    (∑ i ∈ S, (ε * k₁ i + b * (ε * k₂ i) + e * a i * (g * gacc * d i)) + e * g * tacc) • G =
      ε • (∑ i ∈ S, k₁ i • G + b • ∑ i ∈ S, k₂ i • G) +
        e • (g • (gacc • ∑ i ∈ S, a i • (d i • G) + tacc • G)) := by sorry
