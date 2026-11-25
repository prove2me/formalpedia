-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_K_finite_form_one_side
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.smooth_K_finite_form_one_side
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:41:42.953707+00:00
-- url     : https://prove2.me/theorems/3e840ae7-0905-4df3-96ba-e175d0d5175e
-- title:
--   DDSmoothness: smooth K finite form one side
-- statement:
--   The DDSmoothness construction uses the smooth K finite form one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscreteSeriesFormOneReduction.lean#L14-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiscreteSeriesFormOneReduction.lean#L14-L47

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
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

theorem Formalism.FourierDecayAlt.P.DDSmoothness.smooth_K_finite_form_one_side : AtFormOneOfSteps := by sorry
