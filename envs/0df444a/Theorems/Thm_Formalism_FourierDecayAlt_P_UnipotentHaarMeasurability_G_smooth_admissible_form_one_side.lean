-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_G_smooth_admissible_form_one_side
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.smooth_admissible_form_one_side
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:37.742561+00:00
-- url     : https://prove2.me/theorems/47e42929-d28f-5bb9-b7b9-8b52b09ebad9
-- title:
--   G: smooth admissible form one side
-- statement:
--   The G construction uses the smooth admissible form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtFormAdm.lean#L17-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtFormAdm.lean#L17-L65

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdm
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_smooth_admissible_form_one_side

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.G.smooth_admissible_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.AtFormAdmOneOfSteps := by sorry
