-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_eq
-- name    : Formalism.BranchingDeterminantCap.bm_ndE_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:19.420197+00:00
-- url     : https://prove2.me/theorems/0f54495e-f845-4fac-8e4c-8d987d225a82
-- title:
--   Branching Determinant Cap: bm nd E eq
-- statement:
--   The Branching Determinant Cap construction uses the bm nd E eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L314-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L314-L319

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

theorem Formalism.BranchingDeterminantCap.bm_ndE_eq (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) :
    ndE R (n + 1) n l j = bmE R n l j + bmZ R n l j := by sorry
