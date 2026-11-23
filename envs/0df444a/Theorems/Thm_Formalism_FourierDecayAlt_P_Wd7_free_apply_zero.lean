-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_apply_zero
-- name    : Formalism.FourierDecayAlt.P.Wd7.free_apply_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:54.438854+00:00
-- url     : https://prove2.me/theorems/1cdcb4b0-7d14-4758-a04f-0e4253d2451d
-- title:
--   Wd7: free apply zero
-- statement:
--   The Wd7 construction uses the free apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L169-L173

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

theorem Formalism.FourierDecayAlt.P.Wd7.free_apply_zero {a : S} {M : SlopeTestRemainingChoices S A} (hM : FreeOf a M) {z y : Ix S} (h : z a ≠ y a) :
    M z y = 0 := by sorry
