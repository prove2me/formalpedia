-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_liftMatrix_commute_diagScalar
-- name    : Formalism.FourierDecayAlt.P.Wd7.liftMatrix_commute_diagScalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:12.510817+00:00
-- url     : https://prove2.me/theorems/ca6fb14c-4349-4d5d-b59c-9daf103f9127
-- title:
--   Wd7: lift Matrix commute diag Scalar
-- statement:
--   The Wd7 construction uses the lift Matrix commute diag Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L554-L559
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L554-L559

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd7.liftMatrix_commute_diagScalar (Q : M2 A) (b : SlopeTestRemainingChoices S A) (h : ∀ i j, Commute (io (Q i j) : SlopeTestRemainingChoices S A) b) :
    (lift0 Q : M2 (SlopeTestRemainingChoices S A)) * d0 b = d0 b * lift0 Q := by sorry
