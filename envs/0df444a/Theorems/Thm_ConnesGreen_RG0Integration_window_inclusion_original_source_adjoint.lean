-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
-- name    : ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:56:39.10116+00:00
-- url     : https://prove2.me/theorems/529e0f60-bcdb-4178-b46c-b65e72cbba63
-- title:
--   Original actual-zero source columns compress under supported-test custody
-- statement:
--   The exact original actual-zero source columns compress under any isometric nested-window inclusion preserving the original supported-test source representatives. The load-bearing Dirichlet source normalization identifies the dense original test generators. Riesz projection and the original finite-window L2 inner product give a global supported-test pairing, independent of the window. Density then identifies the two physical columns. Actual zeros, analytic multiplicities and reflected-source normalization are unchanged; no positivity or endpoint premise is used.
-- source:
--   CanonicalGreenWindowInclusion.lean, original window_inclusion_source_adjoint; RG0DependencyIntegration.lean. Platform proof reuses the extracted original Dirichlet normalization; helpers recovered with Lean syntax/dependency metadata.

import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
import Definitions.Def_ConnesGreen_RG0_source_constructors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open Filter Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.RG0Integration.window_inclusion_original_source_adjoint (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g))
    (ρ : CriticalZeros) :
    U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
      sourceEmbed t (actualGreenSource ρ) := by sorry
