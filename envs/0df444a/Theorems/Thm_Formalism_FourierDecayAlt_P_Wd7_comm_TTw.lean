-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_TTw
-- name    : Formalism.FourierDecayAlt.P.Wd7.comm_TTw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:22.851984+00:00
-- url     : https://prove2.me/theorems/bb38f5c3-9df8-44f2-acf3-45efd3c954f8
-- title:
--   Wd7: comm TTw
-- statement:
--   The Wd7 construction uses the comm TTw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L531-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L531-L541

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

theorem Formalism.FourierDecayAlt.P.Wd7.comm_TTw (QQ : K → M2 A) (w : List (Letter K S)) (z : A)
    (hz : ∀ Y i j, Commute z (QQ Y i j)) (Y : K) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (TTw QQ w Y i j) := by sorry
