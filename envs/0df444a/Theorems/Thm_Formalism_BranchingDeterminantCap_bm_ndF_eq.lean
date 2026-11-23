-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndF_eq
-- name    : Formalism.BranchingDeterminantCap.bm_ndF_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:30.273713+00:00
-- url     : https://prove2.me/theorems/1d5ffc9e-76bc-4b6e-aa2f-e50d4a498fab
-- title:
--   Branching Determinant Cap: bm nd F eq
-- statement:
--   The Branching Determinant Cap construction uses the bm nd F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L321-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L321-L326

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.bm_ndF_eq (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) :
    ndF R (n + 1) n l j = bmE R n j l + bmZ R n j l := by sorry
