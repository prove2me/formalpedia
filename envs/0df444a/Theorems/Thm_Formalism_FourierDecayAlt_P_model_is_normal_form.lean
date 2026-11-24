-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_model_is_normal_form
-- name    : Formalism.FourierDecayAlt.P.model_is_normal_form
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:24:12.237338+00:00
-- url     : https://prove2.me/theorems/421b6473-4721-47d9-a020-def0252d7691
-- title:
--   P: model is normal form
-- statement:
--   The P construction uses the model is normal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelLevelMultiplier.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelLevelMultiplier.lean#L23-L29

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelLevelMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem Formalism.FourierDecayAlt.P.model_is_normal_form : Formalism.FourierDecayAlt.Q.ModelIsNF := by sorry
