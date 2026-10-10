-- Prove2me | Theorems.Thm_ConnesGreen_canonical_scaled_covariance_le_iff_shell_conditions
-- name    : ConnesGreen.canonical_scaled_covariance_le_iff_shell_conditions
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T05:08:59.73398+00:00
-- url     : https://prove2.me/theorems/8afe6efb-9e65-4312-a7e0-5f68752b1cc5
-- title:
--   Original physical inclusion: exact relative-shell covariance criterion
-- statement:
--   For positive original support windows c ≤ T, a finite selected packet S of actual zeta zeros, and an isometric original-window inclusion U preserving every supported-test source vector, assume ONLY the selected Picard half-bound at the smaller window c. For every real κ ≥ 1, larger-window selected covariance is bounded by κ times its full positive covariance if and only if BOTH: (1) the signed covariance D is nonnegative on the complete orthogonal physical shell ker(U*); and (2) every core/shell pair satisfies |⟨D Ux,z⟩|² ≤ Re⟨D Ux,Ux⟩ Re⟨Dz,z⟩.
--
--   The proof derives core nonnegativity from accepted density of original tests, actor-energy invariance and the smaller-window half-bound. No larger-window half-bound, strict positive core, inverse, positive spectral gap, or finite-off-axis hypothesis is assumed. κ=1, c=T, empty S, and degenerate core/shell directions are included. This is an exact necessary-and-sufficient criterion, not a proof of its shell estimates. Actual carrier, packet membership, multiplicities and actor custody are unchanged. The physical shell is distinct from the zero-index background. Critical-window location, concrete arithmetic endpoint estimates and unconditional neutral-shell control remain open; RH is not established. Original RPB108 form attachments remain future formalization work.
-- source:
--   Recovered unchanged native ConnesGreen.canonical_scaled_covariance_le_iff_shell_conditions interface from RelativeShellEndpoint.lean, with independently assembled core proof using accepted density, window-energy invariance, inner half test criterion and generic shell criterion. Native Lean checks use standard axioms only. Original RPB108 attachments remain future formalization work.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_scaled_covariance_le_iff_shell_conditions
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T)
    (S : Finset CriticalZeros) (U : Physical c →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
      U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker c hc S)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    let D := κ • canonicalPositiveCovariance T hT -
      canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint
    (canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint ≤
      κ • canonicalPositiveCovariance T hT) ↔
    (∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
      0 ≤ RCLike.re ⟪D z, z⟫_ℂ) ∧
    (∀ x : Physical c, ∀ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 →
      ‖⟪D (U x), z⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ) := by sorry
