-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_scalar_commute_transposed_R_matrix_entry
-- name    : Formalism.FourierDecayAlt.P.Wd7.scalar_commute_transposed_R_matrix_entry
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:41.67881+00:00
-- url     : https://prove2.me/theorems/129ab319-6f04-46be-9310-91680147e778
-- title:
--   Wd7: scalar commute transposed R matrix entry
-- statement:
--   The Wd7 construction uses the scalar commute transposed R matrix entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L515-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L515-L524

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

theorem Formalism.FourierDecayAlt.P.Wd7.scalar_commute_transposed_R_matrix_entry (a : S) (D : K) (z : A) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (Rht0 a D i j) := by sorry
