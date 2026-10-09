-- Prove2me | Theorems.Thm_ConnesGreen_canonical_quartet_unshifted_shell_obstruction
-- name    : ConnesGreen.canonical_quartet_unshifted_shell_obstruction
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T18:36:13.445891+00:00
-- url     : https://prove2.me/theorems/a28d07fb-01d0-4219-8830-33661ad2bd60
-- title:
--   Every window beyond an off-line quartet cut has an unshifted shell obstruction
-- statement:
--   Assuming an actual critical-strip zeta zero lies off the critical line, there exists a positive finite core radius c at least the existing small-support radius such that every larger support radius T and every original source-compatible isometric inclusion U have a concrete obstruction for the unchanged unshifted signed quartet covariance D. Either some orthogonal-shell vector has strictly negative D-energy, or some core and orthogonal-shell vectors have squared cross pairing strictly larger than the product of their D-energies. Both alternatives are explicit witnesses on the original completed physical carrier. This theorem does not assert that an off-line zero exists, identify a prescribed endpoint, or prove RH; it localizes exactly which unshifted shell conditions fail past the already certified last good radius.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/QuartetShellExtension.lean at native compiling mathematical-source head 2fe3f23cce4affa88013c4986d573e3000380f3d. Original actors, actual zeta zeros, analytic multiplicities, physical carrier and source custody preserved.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_small_support_constants
open Complex ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem ConnesGreen.canonical_quartet_unshifted_shell_obstruction
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → ∀ U : Physical c →ₗᵢ[ℂ] Physical T,
        (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest c g,
          U (sourceEmbed c (problemOneL g)) = sourceEmbed T (problemOneL g)) →
        let D := canonicalPositiveCovariance T hT -
          canonicalSelectedSynthesis T hT (quartet ρ) ∘L
            (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
        (∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
          RCLike.re ⟪D z, z⟫_ℂ < 0) ∨
        (∃ x : Physical c, ∃ z : Physical T, U.toContinuousLinearMap.adjoint z = 0 ∧
          RCLike.re ⟪D (U x), U x⟫_ℂ * RCLike.re ⟪D z, z⟫_ℂ < ‖⟪D (U x), z⟫_ℂ‖ ^ 2) := by sorry
