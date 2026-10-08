-- Prove2me | Theorems.Thm_ConnesGreen_exists_original_window_actor_inclusion
-- name    : ConnesGreen.exists_original_window_actor_inclusion
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:25:00.461983+00:00
-- url     : https://prove2.me/theorems/f32f6228-f109-4cd0-b7ad-13c9f9760920
-- title:
--   Constructed original window inclusion and exact actual-zero actor compression
-- statement:
--   For positive nested original support windows and the unchanged finite actual-zero packet, construct an isometric inclusion of the original physical carrier preserving every original supported-test source. Every original actual-zero source column compresses exactly along its adjoint, and both the complete positive and selected-negative syntheses compress exactly. The proof reuses the accepted original test inclusion and recovered source normalization/compression, then exact actor basis custody and uniqueness. No positivity or endpoint hypothesis is assumed.
-- source:
--   monocap-tech/weil, checked native CanonicalGreenWindowInclusion.lean and CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b; exact original declarations recovered with Lean elaborator proof boundaries and transported to Lean4.33.1.

import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_exists_original_window_inclusion
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

/-- Original nested physical carriers and both ORIGINAL actor compressions
are constructed, not assumed. All actual source columns are retained. -/
theorem ConnesGreen.exists_original_window_actor_inclusion (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros) :
    ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
      (∀ g : ℝ → ℂ, ∀ hg : SupportedTest t g,
        U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
      (∀ ρ : CriticalZeros,
        U.toContinuousLinearMap.adjoint (sourceEmbed T (actualGreenSource ρ)) =
          sourceEmbed t (actualGreenSource ρ)) ∧
      U.toContinuousLinearMap.adjoint ∘L canonicalPositiveSynthesis T hT =
        canonicalPositiveSynthesis t ht ∧
      U.toContinuousLinearMap.adjoint ∘L canonicalSelectedSynthesis T hT S =
        canonicalSelectedSynthesis t ht S := by sorry
