-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_Xp_fix
-- name    : Formalism.FourierDecayAlt.P.Wd7.Xp_fix
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:55.677646+00:00
-- url     : https://prove2.me/theorems/dc71986b-27e0-4dfc-a9e8-100e6bc79080
-- title:
--   Wd7: Xp fix
-- statement:
--   The Wd7 construction uses the Xp fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L306-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L306-L324

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

theorem Formalism.FourierDecayAlt.P.Wd7.Xp_fix (w : List (Letter K S)) (Y : K) (hr : Reg w Y) (k : Fin 2) (z : Ix S) :
    (Xp w Y k 0 : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0 := by sorry
