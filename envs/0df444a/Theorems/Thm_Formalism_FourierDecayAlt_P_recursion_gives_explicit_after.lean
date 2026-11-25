-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_recursion_gives_explicit_after
-- name    : Formalism.FourierDecayAlt.P.recursion_gives_explicit_after
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:43.610398+00:00
-- url     : https://prove2.me/theorems/de75bccc-2f56-40b7-85a9-1ba8951337a6
-- title:
--   P: recursion gives explicit after
-- statement:
--   The P construction uses the recursion gives explicit after property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L1150-L1150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L1150-L1150

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

theorem Formalism.FourierDecayAlt.P.recursion_gives_explicit_after : Formalism.FourierDecayAlt.TC.RecursionGivesUniformBoundsAfter := by sorry
