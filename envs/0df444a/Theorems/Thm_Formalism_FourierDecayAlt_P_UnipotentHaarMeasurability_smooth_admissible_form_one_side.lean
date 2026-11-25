-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_smooth_admissible_form_one_side
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.smooth_admissible_form_one_side
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:33:47.46443+00:00
-- url     : https://prove2.me/theorems/de9d8190-f997-4323-a07d-5fbc39517a66
-- title:
--   Unipotent Haar Measurability: smooth admissible form one side
-- statement:
--   The Unipotent Haar Measurability construction uses the smooth admissible form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtomicFormOneReduction.lean#L18-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtomicFormOneReduction.lean#L18-L65

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
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

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.smooth_admissible_form_one_side : AtFormAdmOneOfSteps := by sorry
