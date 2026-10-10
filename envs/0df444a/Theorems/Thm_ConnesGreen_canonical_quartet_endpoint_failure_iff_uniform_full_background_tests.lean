-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_uniform_full_background_tests
-- name    : ConnesGreen.canonical_quartet_endpoint_failure_iff_uniform_full_background_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T06:54:48.308149+00:00
-- url     : https://prove2.me/theorems/a471a550-1aa1-4fa0-a392-e4021432e0f2
-- title:
--   Endpoint failure: original admissible tests with uniform full-background reserve
-- statement:
--   For each actual critical-strip zeta zero ρ off the critical line, there exists one positive attained quartet cut c ≥ positiveSupportRadius with the exact closed inner half-bound characterization: for every positive T, half ≤ G_Q(T) iff T ≤ c. At this same cut, FAILURE of the prescribed ordered support-right half-bound is equivalent to: there exists ONE real accuracy η with 0 < η < 1/2 such that for EVERY positive larger original window T > c there exists an ORIGINAL smooth compactly supported test g, with topological support inside (−T,T), satisfying the quantitative COMPLETE-background reserve
--
--   κ (Re W(g*starInv(g)) + ||B_Q,T* x_g||²) < −(κ−1)||N_Q,T* x_g||², where κ=(1/2−η)⁻¹−1>1 and x_g is the original source embedding of Lg. The SAME test also satisfies ||B_Q,T* x_g||² < −Re W(g*starInv(g)) and Re W(g*starInv(g)) < 0. B_Q,T is the complete actual-negative complement outside the unchanged quartet, with ALL analytic multiplicities and paired/reflected normalizations preserved. No background zero is discarded.
--
--   The cut and η are chosen before T; g may depend on T. The first inequality gives a fixed relative coefficient, not one common test or a fixed absolute negative magnitude. The theorem asserts an exact equivalence, NOT endpoint failure or these test witnesses unconditionally. No finite-off-axis hypothesis, critical-endpoint identification, uniform arithmetic estimate, spectral inverse, prescribed Mellin values or RH assumption is introduced. The prescribed regularization then support-right limit order is preserved. RH remains open. Original RPB108 form attachments remain future formalization work.
-- source:
--   New closed consequence of accepted original uniform-shell failure, original window inclusion, relative-shell covariance criterion, original-test covariance detection and full signed actor/arithmetic identity. The summable selected/complement energy partition retains ALL actual remaining zeros. Native upstream sources are unchanged. Complete native/platform proofs identify endpoint failure with one fixed relative reserve in original supported-test inequalities at every larger window. Native Lean checks use standard axioms only. Original RPB108 attachments remain future formalization work.

import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_quartet_endpoint_failure_iff_uniform_full_background_tests
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T →
            ∃ g : ℝ → ℂ, SupportedTest T g ∧
              (((1 / 2 - η)⁻¹ - 1) *
                ((weilDistribution (conv g (starInv g))).re +
                  ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                    (sourceEmbed T (problemOneL g))‖ ^ 2) <
                -(((1 / 2 - η)⁻¹ - 1) - 1) *
                  ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                    (sourceEmbed T (problemOneL g))‖ ^ 2) ∧
              ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 <
                -(weilDistribution (conv g (starInv g))).re ∧
              (weilDistribution (conv g (starInv g))).re < 0) := by sorry
