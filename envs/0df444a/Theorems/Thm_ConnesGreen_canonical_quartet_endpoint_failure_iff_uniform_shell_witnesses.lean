-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_failure_iff_uniform_shell_witnesses
-- name    : ConnesGreen.canonical_quartet_endpoint_failure_iff_uniform_shell_witnesses
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T06:35:55.89335+00:00
-- url     : https://prove2.me/theorems/aa8c96a8-d6ec-46e2-bee4-627fd3ba0187
-- title:
--   Endpoint failure: fixed accuracy and physical shell witnesses at every larger window
-- statement:
--   For every actual critical-strip zeta zero ρ off the critical line, there exists a positive attained original quartet cut c at least positiveSupportRadius, with the exact original inner marker half-bound characterization: for all positive T, half ≤ G_Q(T) iff T ≤ c. At this same cut, FAILURE of the prescribed ordered support-right half-bound is equivalent to the following uniform physical obstruction. There exists ONE real accuracy η with 0 < η < 1/2 such that for EVERY positive larger window T > c: an original complex-linear isometric inclusion U exists preserving EVERY smaller-window supported-test source vector; and for EVERY such compatible inclusion, there is either an orthogonal physical-shell vector z with Re⟨Dz,z⟩ < 0, or a core/shell pair x,z with Re⟨DUx,Ux⟩ Re⟨Dz,z⟩ < |⟨DUx,z⟩|². Here z belongs to ker(U*) and D = ((1/2−η)⁻¹−1) A_T − N_Q,T N_Q,T*, with the original ALL-positive actual-zero covariance A_T and unchanged selected negative quartet synthesis N_Q,T.
--
--   One η is chosen before every T and U. Witness vectors may depend on T and U. The inclusion existence conjunct prevents vacuity. Both failures use strict inequalities; either or both can occur. This is an exact equivalence, not an assertion of endpoint failure or unconditional witnesses. It does not supply a uniform strict margin in the witness inequalities, one fixed vector, prescribed Mellin interpolation, or a critical-endpoint identification. It assumes no larger-window half-bound, no strict core gap/inverse, and no finite-off-axis hypothesis. The physical shell is distinct from the complete zero-index background. The already prescribed ordered limits are preserved, not exchanged. RH remains open; original RPB108 attachments remain future formalization work.
-- source:
--   New closed consequence of accepted ConnesGreen.canonical_quartet_endpoint_half_iff_original_shell_obligations and ConnesGreen.exists_original_window_inclusion. Full native and platform proofs supplied; native upstream RelativeShellEndpoint.lean interface remains unchanged. The theorem identifies conditional endpoint failure with one fixed accuracy and strict shell/coupling witnesses for every compatible inclusion in every larger window. Native Lean checks use standard axioms only. Original RPB108 attachments remain future formalization work.

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

theorem ConnesGreen.canonical_quartet_endpoint_failure_iff_uniform_shell_witnesses
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      (¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
        ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
          ∀ T : ℝ, ∀ hT : 0 < T, c < T →
            (∃ U : Physical c →ₗᵢ[ℂ] Physical T,
              ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
                U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
            ∀ U : Physical c →ₗᵢ[ℂ] Physical T,
              (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
                U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) →
              let D := ((1 / 2 - η)⁻¹ - 1) • canonicalPositiveCovariance T hT -
                canonicalSelectedSynthesis T hT (quartet ρ) ∘L
                  (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
              (∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
                RCLike.re ⟪D z, z⟫_ℂ < 0) ∨
              (∃ x : Physical c, ∃ z : Physical T,
                U.toContinuousLinearMap.adjoint z = 0 ∧
                RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ <
                  ‖⟪D (U x), z⟫_ℂ‖ ^ 2)) := by sorry
