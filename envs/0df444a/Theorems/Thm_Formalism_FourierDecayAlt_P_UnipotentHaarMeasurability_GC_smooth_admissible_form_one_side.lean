-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_GC_smooth_admissible_form_one_side
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.GC.smooth_admissible_form_one_side
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:08:50.978443+00:00
-- url     : https://prove2.me/theorems/119402cf-f6ba-58e9-a0ca-150c9483b22e
-- title:
--   GC: smooth admissible form one side
-- statement:
--   The GC construction uses the smooth admissible form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtFormAdmC.lean#L17-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/BesselOrbitConvolutions/AtFormAdmC.lean#L17-L64

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdmOneOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdmC
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
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.GC

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.GC.smooth_admissible_form_one_side : CompanionTheory.D.Upq.BesselFunctionalConstruction.C.AtFormAdmOneOfSteps := by sorry
