-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_intertwiner_commute
-- name    : CompanionTheory.D.Upq.Sm.intertwiner_commute
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:09.208167+00:00
-- url     : https://prove2.me/theorems/e9fdf081-9c26-4175-bb76-be8ed702fb59
-- title:
--   Sm: intertwiner commute
-- statement:
--   The Sm construction uses the intertwiner commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L172-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L172-L194

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Convolution
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {hG : IsMatGroup G}
open PI.UpqRep

theorem CompanionTheory.D.Upq.Sm.intertwiner_commute : Formalism.FourierDecayAlt.ThreeDimData.IntCommute := by sorry
