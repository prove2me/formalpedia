-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_lower_splitting_measurable
-- name    : Formalism.FourierDecayAlt.P.lower_splitting_measurable
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:44.154703+00:00
-- url     : https://prove2.me/theorems/793556d5-3c9b-42ad-a3ee-60dc5fb1deaf
-- title:
--   P: lower splitting measurable
-- statement:
--   The P construction uses the lower splitting measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L276-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShearMeasurability.lean#L276-L285

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open ShearMeasurability

theorem Formalism.FourierDecayAlt.P.lower_splitting_measurable : C2.LowSplitMeas := by sorry
