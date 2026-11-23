-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_omg_add
-- name    : Formalism.BranchingDeterminantCap.bmF_omg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:53.284318+00:00
-- url     : https://prove2.me/theorems/c0264a19-052e-49f1-9b42-2fb93d8424d2
-- title:
--   Branching Determinant Cap: bm F omg add
-- statement:
--   The Branching Determinant Cap construction uses the bm F omg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1585-L1586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1585-L1586

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

theorem Formalism.BranchingDeterminantCap.bmF_omg_add {n : ℕ} (β β' : Fin n → ℤ) : omg (β + β') = omg β + omg β' := by sorry
