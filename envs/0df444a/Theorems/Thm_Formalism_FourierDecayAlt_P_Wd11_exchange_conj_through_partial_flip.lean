-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_exchange_conj_through_partial_flip
-- name    : Formalism.FourierDecayAlt.P.Wd11.exchange_conj_through_partial_flip
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:49.24633+00:00
-- url     : https://prove2.me/theorems/15f5aa6d-fae0-4a8c-9899-6b5861ebb3b2
-- title:
--   Wd11: exchange conj through partial flip
-- statement:
--   The Wd11 construction uses the exchange conj through partial flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L265-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L265-L273

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

theorem Formalism.FourierDecayAlt.P.Wd11.exchange_conj_through_partial_flip (b : S) (s : K) :
    d0 (ins b (lift0 (Um (A := A) (star s)))) * Q0 b * lift0 (Um (A := A) s)ᴴ =
      lift0 (Um (A := A) s)ᴴ * Q0 b * d0 (ins b (lift0 (Um (A := A) (star s)))) := by sorry
