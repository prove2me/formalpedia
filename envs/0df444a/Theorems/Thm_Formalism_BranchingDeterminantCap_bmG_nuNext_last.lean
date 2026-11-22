-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_last
-- name    : Formalism.BranchingDeterminantCap.bmG_nuNext_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:46.97921+00:00
-- url     : https://prove2.me/theorems/f6fa4cad-32c3-428f-8555-dd27d0fd8bc4
-- title:
--   Branching Determinant Cap: bm G nu Next last
-- statement:
--   The Branching Determinant Cap construction uses the bm G nu Next last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2033-L2035
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2033-L2035

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

theorem Formalism.BranchingDeterminantCap.bmG_nuNext_last {n : ℕ} (ν : Fin n → ℕ) (i : Fin n) (h : ¬ i.val + 1 < n) : nuNext ν i = 0 := by sorry
