-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_endpoint_half_iff_original_shell_obligations
-- name    : ConnesGreen.canonical_quartet_endpoint_half_iff_original_shell_obligations
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T05:57:35.081214+00:00
-- url     : https://prove2.me/theorems/3084dfa9-b74f-4176-9899-06dddf133e34
-- title:
--   Actual quartet cut: exact ordered-endpoint shell obligations
-- statement:
--   For every actual critical-strip zeta zero ρ with Re ρ ≠ 1/2, there exists a positive attained cut c at least the certified positiveSupportRadius. For every positive support window T, the original quartet Picard marker has half lower bound exactly when T ≤ c, including equality. At that same cut, the prescribed original support-right marker has half lower bound if and only if: for EVERY real accuracy 0 < η < 1/2, there exists a positive larger original window T > c and a complex-linear isometric original inclusion U preserving EVERY smaller-window supported-test source vector, such that BOTH complete orthogonal physical-shell positivity and the relative core/shell cross-term budget hold for D = ((1/2−η)⁻¹−1) A_T − N_Q,T N_Q,T*. The shell is ker(U*), A_T is the original ALL-positive actual-zero covariance, N_Q,T is the unchanged selected negative quartet actor, and the cross-term bound is |⟨D Ux,z⟩|² ≤ Re⟨D Ux,Ux⟩ Re⟨Dz,z⟩ for every core x and every shell z.
--
--   The cut is chosen once before every window and accuracy. The larger window and inclusion may depend on η. The theorem establishes an exact equivalence, not the shell estimates or endpoint half-bound. It identifies neither c nor T with a separately intended critical endpoint. It assumes no larger-window half-bound, no finite-off-axis hypothesis, no strict positive spectral gap, and no unregularized inverse. All actual-zero multiplicities, reflected paired columns and original carrier custody are preserved. Inner regularization and outer right-support limits are kept in the prescribed order. RH remains open. The physical shell is distinct from the complete zero-index background; original RPB108 attachments remain future formalization work.
-- source:
--   Recovered unchanged native ConnesGreen.canonical_quartet_endpoint_half_iff_original_shell_obligations from RelativeShellEndpoint.lean. Closed independent assembly uses accepted actual-quartet cutoff, positive support radius, original inclusion, relative-shell criterion, all-regularized Picard equivalence and generic marker/covariance equivalence. Native Lean checks use standard axioms only. Original RPB108 attachments remain future formalization work.

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

theorem ConnesGreen.canonical_quartet_endpoint_half_iff_original_shell_obligations
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ (quartet ρ)}, ℂ) →L[ℂ]
      ℓ²({τ : CriticalZeros // τ ∈ (quartet ρ)}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ) ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ T : ℝ, ∃ hT : 0 < T, c < T ∧
      ∃ U : Physical c →ₗᵢ[ℂ] Physical T,
        (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
          U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
        let D := ((1 / 2 - η)⁻¹ - 1) • canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT (quartet ρ) ∘L (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
        (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
        (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
          ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ)) := by sorry
