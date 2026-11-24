-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Viw_cons
-- name    : Formalism.FourierDecayAlt.P.Wd11.Viw_cons
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:47:58.861781+00:00
-- url     : https://prove2.me/theorems/3a3ad56e-d484-4fcf-80f6-895c3338fbd5
-- title:
--   Wd11: Viw cons
-- statement:
--   The Wd11 construction uses the Viw cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L565-L570
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L565-L570

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd11.Viw_cons (fi : A) (s : K) (l : Letter K S) (w : List (Letter K S)) :
    Viw fi s (l :: w) =
      ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * Viw fi s w := by sorry
