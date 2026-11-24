-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_diagonal_eq_diagScalar
-- name    : Formalism.FourierDecayAlt.P.Wd11.liftMatrix_diagonal_eq_diagScalar
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:03.318728+00:00
-- url     : https://prove2.me/theorems/b211380f-d6d2-4973-a96a-accd6be59e91
-- title:
--   Wd11: lift Matrix diagonal eq diag Scalar
-- statement:
--   The Wd11 construction uses the lift Matrix diagonal eq diag Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L93-L96

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

theorem Formalism.FourierDecayAlt.P.Wd11.liftMatrix_diagonal_eq_diagScalar (f : A) : (lift0 (Matrix.diagonal fun _ => f) : M2 (SlopeTestRemainingChoices S A)) = d0 (io f) := by sorry
