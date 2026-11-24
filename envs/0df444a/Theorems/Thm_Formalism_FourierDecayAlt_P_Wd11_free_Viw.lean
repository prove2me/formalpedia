-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_Viw
-- name    : Formalism.FourierDecayAlt.P.Wd11.free_Viw
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:48:06.638776+00:00
-- url     : https://prove2.me/theorems/1d41326b-e3dc-4a98-8f6d-7df12324aab8
-- title:
--   Wd11: free Viw
-- statement:
--   The Wd11 construction uses the free Viw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L425-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L425-L426

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

theorem Formalism.FourierDecayAlt.P.Wd11.free_Viw (fi : A) (s : K) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (Viw fi s w) := by sorry
