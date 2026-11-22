-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_zW_castSucc
-- name    : Formalism.BranchingDeterminantCap.bmF_zW_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:31.631837+00:00
-- url     : https://prove2.me/theorems/ba5f585d-3e98-46b2-adc8-459e782eab62
-- title:
--   Branching Determinant Cap: bm F z W cast Succ
-- statement:
--   The Branching Determinant Cap construction uses the bm F z W cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1684-L1685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1684-L1685

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

theorem Formalism.BranchingDeterminantCap.bmF_zW_castSucc {n : ℕ} (a s : Fin n) : zW n (a.castSucc, s) = 0 := by sorry
