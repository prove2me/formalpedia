-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_transpose_mul_of_comm
-- name    : Formalism.FourierDecayAlt.P.Wd7.transpose_mul_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:26.998357+00:00
-- url     : https://prove2.me/theorems/fba56815-0cf7-4d65-b1d4-cd89735ccdd0
-- title:
--   Wd7: transpose mul of comm
-- statement:
--   The Wd7 construction uses the transpose mul of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L443-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L443-L447

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transpose_mul_of_comm

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

theorem Formalism.FourierDecayAlt.P.Wd7.transpose_mul_of_comm {B : Type} [Ring B] (M N : M2 B)
    (h : ∀ i j k l, Commute (M i j) (N k l)) : (M * N)ᵀ = Nᵀ * Mᵀ := by sorry
