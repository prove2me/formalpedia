-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmA_cast_comm
-- name    : Formalism.BranchingDeterminantCap.bmA_cast_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:50.985811+00:00
-- url     : https://prove2.me/theorems/9f03e309-3d15-44da-a4b2-2b591a8608f6
-- title:
--   Branching Determinant Cap: bm A cast comm
-- statement:
--   The Branching Determinant Cap construction uses the bm A cast comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L602-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L602-L604

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem Formalism.BranchingDeterminantCap.bmA_cast_comm (z : ℤ) (X : Module.End R M) :
    ((z : ℤ) : Module.End R M) * X = X * ((z : ℤ) : Module.End R M) := by sorry
