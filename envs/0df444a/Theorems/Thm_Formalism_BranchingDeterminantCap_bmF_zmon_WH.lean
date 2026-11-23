-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zmon_WH
-- name    : Formalism.BranchingDeterminantCap.bmF_zmon_WH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:26.8198+00:00
-- url     : https://prove2.me/theorems/22e6fe79-b929-42e4-ada6-ce56a42f44d8
-- title:
--   Branching Determinant Cap: bm F zmon WH
-- statement:
--   The Branching Determinant Cap construction uses the bm F zmon WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1657-L1665
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1657-L1665

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

theorem Formalism.BranchingDeterminantCap.bmF_zmon_WH (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) :
    IsWeightedHomogeneous (zW n) (zmon R n b) (fun s => (b s : ℤ)) := by sorry
