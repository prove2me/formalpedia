-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_theorem_a_after_of_parts
-- name    : Formalism.FourierDecayAlt.P.theorem_a_after_of_parts
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:31.317646+00:00
-- url     : https://prove2.me/theorems/7325f5bf-559a-4f48-b44c-9c8a56005a3d
-- title:
--   P: theorem a after of parts
-- statement:
--   The P construction uses the theorem a after of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L1124-L1124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L1124-L1124

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open RecursionWithDensities

theorem Formalism.FourierDecayAlt.P.theorem_a_after_of_parts : Formalism.FourierDecayAlt.TC.TheoremAAfterOfSteps := by sorry
