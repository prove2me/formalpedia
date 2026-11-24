-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_insert_mul_diagScalar
-- name    : Formalism.FourierDecayAlt.P.Wd7.insert_mul_diagScalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:39.867026+00:00
-- url     : https://prove2.me/theorems/f9bcabd4-f156-4a9a-9fcf-2d2da0a637ff
-- title:
--   Wd7: insert mul diag Scalar
-- statement:
--   The Wd7 construction uses the insert mul diag Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L135-L137

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd7.insert_mul_diagScalar (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) : ins a (M * d0 b) = ins a M * b := by sorry
