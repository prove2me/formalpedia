-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_ins_sandwich
-- name    : Formalism.FourierDecayAlt.P.Wd11.ins_sandwich
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:46:34.021805+00:00
-- url     : https://prove2.me/theorems/7be0bff8-98fa-4c78-b813-d2bfd2cd85eb
-- title:
--   Wd11: ins sandwich
-- statement:
--   The Wd11 construction uses the ins sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L143-L149

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd11.ins_sandwich {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (M : M2 (SlopeTestRemainingChoices S A)) (y : SlopeTestRemainingChoices S A) :
    ins a (d0 x * M * d0 y) = x * ins a M * y := by sorry
