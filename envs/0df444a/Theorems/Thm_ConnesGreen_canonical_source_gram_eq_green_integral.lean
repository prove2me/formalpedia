-- Prove2me | Theorems.Thm_ConnesGreen_canonical_source_gram_eq_green_integral
-- name    : ConnesGreen.canonical_source_gram_eq_green_integral
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T21:44:03.127465+00:00
-- url     : https://prove2.me/theorems/7968e6c2-e739-45db-befa-b6dea346184d
-- title:
--   Original physical Green-column pairing equals its Green/source interval integral
-- statement:
--   For every positive original support radius and every two actual zeta zeros in the critical strip, the inner product of their original source embeddings in the completed Dirichlet carrier is exactly the interval integral of conjugate(actualGreenSource ρ) times greenColumn t σ on [−t,t]. The orientation is fixed by the first slot of the complex inner product. No abstract zero replacement, transform renormalization, carrier change, multiplicity alteration, positivity assumption, or RH assumption occurs.
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

theorem ConnesGreen.canonical_source_gram_eq_green_integral (t : ℝ) (ht : 0 < t)
    (ρ σ : CriticalZeros) :
    ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (actualGreenSource σ)⟫_ℂ =
      canonicalSourceGramKernel t ρ σ := by sorry
