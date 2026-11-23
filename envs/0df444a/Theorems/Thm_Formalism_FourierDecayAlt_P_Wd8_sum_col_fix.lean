-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_sum_col_fix
-- name    : Formalism.FourierDecayAlt.P.Wd8.sum_col_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:29.654523+00:00
-- url     : https://prove2.me/theorems/ec77ec99-8cd7-4c15-8196-6f5e19ad3c8d
-- title:
--   Wd8: sum col fix
-- statement:
--   The Wd8 construction uses the sum col fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L311-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L311-L316

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd8.sum_col_fix (B C : Fin 2 → SlopeTestRemainingChoices S A) (z : Ix S)
    (h : ∀ (k : Fin 2) (z' : Ix S), C k z' e1 = if k = 0 ∧ z' = e1 then 1 else 0) :
    (∑ k, B k * C k) z e1 = B 0 z e1 := by sorry
