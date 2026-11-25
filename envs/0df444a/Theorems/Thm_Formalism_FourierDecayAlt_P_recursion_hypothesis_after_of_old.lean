-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_recursion_hypothesis_after_of_old
-- name    : Formalism.FourierDecayAlt.P.recursion_hypothesis_after_of_old
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:10.781205+00:00
-- url     : https://prove2.me/theorems/0eea4160-f2af-56fc-aa9a-e3221938ee62
-- title:
--   P: recursion hypothesis after of old
-- statement:
--   The P construction uses the recursion hypothesis after of old property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L1148-L1148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L1148-L1148

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

theorem Formalism.FourierDecayAlt.P.recursion_hypothesis_after_of_old : Formalism.FourierDecayAlt.TC.RecHypAfterOfOld := by sorry
