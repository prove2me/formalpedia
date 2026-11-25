-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_position_block_minus
-- name    : Formalism.FourierDecayAlt.P.position_block_minus
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:49.836057+00:00
-- url     : https://prove2.me/theorems/36fcf666-0c67-503d-9a43-000bb8e97ba1
-- title:
--   P: position block minus
-- statement:
--   The P construction uses the position block minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L211-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L211-L220

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.position_block_minus : Formalism.FourierDecayAlt.Fr.TransposedCoordinateBlockCondition := by sorry
