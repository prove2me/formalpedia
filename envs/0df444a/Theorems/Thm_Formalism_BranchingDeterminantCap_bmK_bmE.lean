-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_bmE
-- name    : Formalism.BranchingDeterminantCap.bmK_bmE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:20.198472+00:00
-- url     : https://prove2.me/theorems/0706a1ca-db5c-4893-a015-5d8f39bfaa66
-- title:
--   Branching Determinant Cap: bm K bm E
-- statement:
--   The Branching Determinant Cap construction uses the bm K bm E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2407-L2409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2407-L2409

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

theorem Formalism.BranchingDeterminantCap.bmK_bmE (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (k l : Fin n) (u : ℤ) (G : BP R n) :
    bmE R n k l (bmCap R n u G) = bmCap R n u (bmE R n k l G) := by sorry
