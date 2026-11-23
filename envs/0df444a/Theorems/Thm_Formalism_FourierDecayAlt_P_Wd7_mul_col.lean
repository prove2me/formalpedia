-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_col
-- name    : Formalism.FourierDecayAlt.P.Wd7.mul_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:10.563337+00:00
-- url     : https://prove2.me/theorems/d0aeeddb-38cb-4723-86f4-0fd5323ff60a
-- title:
--   Wd7: mul col
-- statement:
--   The Wd7 construction uses the mul col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L298-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L298-L304

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

theorem Formalism.FourierDecayAlt.P.Wd7.mul_col (M N : M2 (SlopeTestRemainingChoices S A))
    (hN : ∀ (m : Fin 2) (z : Ix S), (N m 0) z e1 = if m = 0 ∧ z = e1 then 1 else 0)
    (k : Fin 2) (z : Ix S) : ((M * N) k 0) z e1 = (M k 0) z e1 := by sorry
