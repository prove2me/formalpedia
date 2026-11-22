-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_lastW_castSucc
-- name    : Formalism.BranchingDeterminantCap.bmF_lastW_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:48.156617+00:00
-- url     : https://prove2.me/theorems/e441ccbc-ea09-41a5-91f6-26dabd1d9167
-- title:
--   Branching Determinant Cap: bm F last W cast Succ
-- statement:
--   The Branching Determinant Cap construction uses the bm F last W cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1687-L1688
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1687-L1688

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

theorem Formalism.BranchingDeterminantCap.bmF_lastW_castSucc {n : ℕ} (a s : Fin n) : lastW n (a.castSucc, s) = 0 := by sorry
