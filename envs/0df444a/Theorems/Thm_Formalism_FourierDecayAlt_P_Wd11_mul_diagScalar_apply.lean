-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_mul_diagScalar_apply
-- name    : Formalism.FourierDecayAlt.P.Wd11.mul_diagScalar_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:47:40.469474+00:00
-- url     : https://prove2.me/theorems/cd24cfc2-afa0-4290-aadb-0611f31303f5
-- title:
--   Wd11: mul diag Scalar apply
-- statement:
--   The Wd11 construction uses the mul diag Scalar apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L69-L71

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

theorem Formalism.FourierDecayAlt.P.Wd11.mul_diagScalar_apply (x : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2) :
    (M * d0 x) i j = M i j * x := by sorry
