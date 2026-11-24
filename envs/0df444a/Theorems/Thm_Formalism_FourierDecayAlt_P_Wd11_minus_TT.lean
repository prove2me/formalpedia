-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_minus_TT
-- name    : Formalism.FourierDecayAlt.P.Wd11.minus_TT
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:15.428831+00:00
-- url     : https://prove2.me/theorems/0da9e3b6-0764-4638-a732-66a029a466cd
-- title:
--   Wd11: minus TT
-- statement:
--   The Wd11 construction uses the minus TT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L495-L521
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L495-L521

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

theorem Formalism.FourierDecayAlt.P.Wd11.minus_TT (b : S) (s d : K) {V Vi : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf b V) (hVi : FreeOf b Vi) (hT : FreeOf2 b T)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    d0 (ins b (lift0 (Um (A := A) (star s))) * Vi) * (Rht0 b d * T) *
        d0 (ins b (lift0 (Uinv (A := A) (star s))) * V) =
      lift0 (Um (A := A) s)ᴴ * (Rht0 b d * T) * lift0 (Um (A := A) s) := by sorry
