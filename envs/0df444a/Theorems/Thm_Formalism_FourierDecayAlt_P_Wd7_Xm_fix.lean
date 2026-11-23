-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Xm_fix
-- name    : Formalism.FourierDecayAlt.P.Wd7.Xm_fix
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:12.306611+00:00
-- url     : https://prove2.me/theorems/1791ebdf-cc46-4a6c-a967-34d90f42aa0b
-- title:
--   Wd7: Xm fix
-- statement:
--   The Wd7 construction uses the Xm fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L346-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L346-L367

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

theorem Formalism.FourierDecayAlt.P.Wd7.Xm_fix (w : List (Letter K S)) (Y : K) (hn : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : Reg w Y)
    (k : Fin 2) (z : Ix S) :
    (Xm w Y 0 k : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0 := by sorry
