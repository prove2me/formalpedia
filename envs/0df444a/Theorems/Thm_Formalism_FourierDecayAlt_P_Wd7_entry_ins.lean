-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_entry_ins
-- name    : Formalism.FourierDecayAlt.P.Wd7.entry_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:42.613975+00:00
-- url     : https://prove2.me/theorems/ad231c57-fa99-4579-9819-3873658c7e4e
-- title:
--   Wd7: entry ins
-- statement:
--   The Wd7 construction uses the entry ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L376-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L376-L390

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

theorem Formalism.FourierDecayAlt.P.Wd7.entry_ins (a : S) (R : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (hR : FreeOf a R) (hM : FreeOf2 a M) :
    (R * ins a M) e1 e1 = (R * M 0 0) e1 e1 := by sorry
