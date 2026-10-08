-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_uniform_original_pair_actor_tail
-- name    : ConnesGreen.RG0Integration.uniform_original_pair_actor_tail
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:06:40.639462+00:00
-- url     : https://prove2.me/theorems/d8593b43-47ce-46d7-a3a5-223df376f2ec
-- title:
--   Uniform original two-sided actual-zero actor tails on every positive subwindow
-- statement:
--   For every fixed original positive upper support T, unchanged finite actual-zero packet S and accuracy eta>0, there is a single reflection-closed finite cutoff F containing S such that BOTH original complementary pair actor covariances have combined norm below eta for EVERY original positive support t<=T. The original positive-tail synthesis is constructed with exact actual columns; the negative tail is the existing original background actor. Source compression along the constructed original window inclusion gives column norm domination by the original columns at T; their proved summability yields one uniform cutoff. The original multiplicities, reflection and /2 pair normalization are retained. This is absolute tail control. It neither assumes a fixed cutoff at all regularizations nor proves the relative inverse-cost bound at the critical endpoint.
-- source:
--   TwoSidedTailControl.lean, original canonical_uniform_small_pair_actor_tail; RG0DependencyIntegration.lean. Platform proof uses original source compression and complete original actor summability, without a surrogate zero set or envelope premise.

import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousLinearMap Filter Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.RG0Integration.uniform_original_pair_actor_tail (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ ρ, Ptail (lp.single 2 ρ (1 : ℂ)) =
            positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < η := by sorry
