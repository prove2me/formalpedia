-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_iff_integral_gram_certificates
-- name    : ConnesGreen.canonical_picard_half_iff_integral_gram_certificates
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T21:44:07.862983+00:00
-- url     : https://prove2.me/theorems/fc4ced04-19a2-47e1-b8ff-8161e9e37511
-- title:
--   Original inner half-bound is equivalent to explicit integral Gram certificates
-- statement:
--   At one fixed positive original support window and unchanged selected actual-zero packet S, the inner Picard marker is at least half the identity exactly when for every positive error allowance δ there exists a finite reflection-closed actual-zero packet F containing S with complete positive diagonal-kernel tail less than δ and positive semidefinite matrix δH + H E H. H consists entirely of the explicit Green/source pair integrals with original square-root multiplicities, reflection duplication, and /2 column normalization. E records positive F tags +1 and negative S tags −1. The diagonal-kernel tail is exactly the original full positive-column norm-square tail. The error term is δH, accounting for possibly dependent and nonorthonormal columns. The window is fixed before accuracy varies. This certifies an exact integral target; it does not prove its PSD estimates, larger-window extension, or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteIntegralGram.lean at compiling source head d81aa3cc2a387fa9f51ee06fee978b868cbc6b85

import Definitions.Def_ConnesGreen_integral_certificate_kernel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative MeasureTheory Matrix
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.canonical_picard_half_iff_integral_gram_certificates
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        (canonicalPairGramKernel t 1 1 ρ.1 ρ.1).re) < δ ∧
      (canonicalFiniteIntegralCertificate t S F δ).PosSemidef := by sorry
