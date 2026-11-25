-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_BM_discrete_form_one_side
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.BM.discrete_form_one_side
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:46:56.261872+00:00
-- url     : https://prove2.me/theorems/b86f721e-0c6c-5e79-bf43-04cdc648a2af
-- title:
--   BM: discrete form one side
-- statement:
--   The BM construction uses the discrete form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/DDForm.lean#L15-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/DDForm.lean#L15-L45

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_DDForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_discrete_form_one_side

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.DDSmoothness.BM

theorem Formalism.FourierDecayAlt.P.DDSmoothness.BM.discrete_form_one_side : CompanionTheory.Lime.BM.DDFormOneOfSteps := by sorry
