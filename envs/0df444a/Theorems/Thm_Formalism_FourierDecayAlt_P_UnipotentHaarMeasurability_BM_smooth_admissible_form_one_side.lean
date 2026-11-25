-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_BM_smooth_admissible_form_one_side
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.BM.smooth_admissible_form_one_side
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:50.286904+00:00
-- url     : https://prove2.me/theorems/ffd0900d-be71-5744-8228-138c4ab95b97
-- title:
--   BM: smooth admissible form one side
-- statement:
--   The BM construction uses the smooth admissible form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdm.lean#L17-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdm.lean#L17-L64

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdm
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
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.BM

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.BM.smooth_admissible_form_one_side : CompanionTheory.Lime.BM.AtFormAdmOneOfSteps := by sorry
