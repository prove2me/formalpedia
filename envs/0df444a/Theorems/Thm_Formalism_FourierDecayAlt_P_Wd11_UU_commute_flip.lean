-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_UU_commute_flip
-- name    : Formalism.FourierDecayAlt.P.Wd11.UU_commute_flip
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:47:36.546718+00:00
-- url     : https://prove2.me/theorems/7f012996-28b1-4646-a0a3-f66a9829109a
-- title:
--   Wd11: UU commute flip
-- statement:
--   The Wd11 construction uses the UU commute flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L256-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L256-L263

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

theorem Formalism.FourierDecayAlt.P.Wd11.UU_commute_flip (a : S) (s : K) :
    lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))) * P0 a =
      P0 a * (lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s)))) := by sorry
