-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf_positive_word_matrix
-- name    : Formalism.FourierDecayAlt.P.Wd7.freeOf_positive_word_matrix
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:58.765752+00:00
-- url     : https://prove2.me/theorems/622beabc-7ba7-432b-a73f-057706f7b4ae
-- title:
--   Wd7: free Of positive word matrix
-- statement:
--   The Wd7 construction uses the free Of positive word matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L230-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L230-L240

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

theorem Formalism.FourierDecayAlt.P.Wd7.freeOf_positive_word_matrix {c : S} (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) (Y : K) :
    FreeOf2 c (Xp w Y : M2 (SlopeTestRemainingChoices S A)) := by sorry
