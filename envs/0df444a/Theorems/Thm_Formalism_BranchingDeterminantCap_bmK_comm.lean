-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_comm
-- name    : Formalism.BranchingDeterminantCap.bmK_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:29.622143+00:00
-- url     : https://prove2.me/theorems/6ffd1659-eee9-4d87-bc66-1f00548efbd7
-- title:
--   Branching Determinant Cap: bm K comm
-- statement:
--   The Branching Determinant Cap construction uses the bm K comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2403-L2405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2403-L2405

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

theorem Formalism.BranchingDeterminantCap.bmK_comm (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (u v : ℤ) :
    Commute (bmCap R n u) (bmCap R n v) := by sorry
