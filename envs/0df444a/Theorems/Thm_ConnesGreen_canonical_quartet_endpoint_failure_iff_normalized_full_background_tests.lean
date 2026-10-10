-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_normalized_full_background_tests
-- name    : ConnesGreen.canonical_quartet_endpoint_failure_iff_normalized_full_background_tests
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T07:13:49.069108+00:00
-- url     : https://prove2.me/theorems/9d08a6f2-972b-40cf-82ae-9d1c54a74b50
-- title:
--   Endpoint failure: unit-quartet tests with a uniform complete-background margin
-- statement:
--   For every actual critical-strip zeta zero off the critical line, there is a positive attained quartet cut c at or beyond the positive support radius. The exact original inner half-bound holds precisely at positive windows T ≤ c. At that SAME cut, failure of the right-support endpoint half-bound is equivalent to the existence of ONE δ with 0 < δ < 1, such that EVERY positive window T > c admits an ORIGINAL supported admissible test g with selected quartet adjoint energy exactly one, Re W(g*starInv g) plus the adjoint energy of the COMPLETE actual unselected-negative background strictly below −δ, and Re W(g*starInv g) strictly below −δ. The test may vary with T. This asserts neither endpoint failure nor unconditional existence of these tests; the margin is obtained only after fixing the selected energy scale. It asserts no bounded physical norm, prescribed Mellin values, finite-off-axis classification, changed zero indexing, or RH.
-- source:
--   New closed consequence of accepted uniform full-background witness criterion, accepted original source/energy identity, and accepted full signed arithmetic identity. Normalization acts on ORIGINAL supported admissible tests, preserves their differential source and all actual selected/background actor energies, and proves selected energy is nonzero before inversion. A single margin delta in (0,1) serves all windows above the attained cut after selected quartet energy is fixed to one. This is conditional on endpoint failure; no critical-window location or endpoint failure is asserted, and no physical-norm boundedness is claimed. Native source unchanged. Original RPB108 attachments remain future formalization.

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

theorem ConnesGreen.canonical_quartet_endpoint_failure_iff_normalized_full_background_tests
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T →
            ∃ g : ℝ → ℂ, SupportedTest T g ∧
              ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                (sourceEmbed T (problemOneL g))‖ ^ 2 = 1 ∧
              (weilDistribution (conv g (starInv g))).re +
                ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 < -δ ∧
              (weilDistribution (conv g (starInv g))).re < -δ) := by sorry
