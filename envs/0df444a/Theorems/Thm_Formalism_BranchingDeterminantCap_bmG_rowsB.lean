-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_rowsB
-- name    : Formalism.BranchingDeterminantCap.bmG_rowsB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:28.735796+00:00
-- url     : https://prove2.me/theorems/7a7a7adf-5a54-4d70-8f7f-e3e43492118c
-- title:
--   Branching Determinant Cap: bm G rows B
-- statement:
--   The Branching Determinant Cap construction uses the bm G rows B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2237-L2246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2237-L2246

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

theorem Formalism.BranchingDeterminantCap.bmG_rowsB {n : ℕ} (i : Fin n) :
    (rowsB i : Fin (i.val + 1) → Fin (n + 1)) =
      fun p => if h : p.val < i.val then (Fin.castLE (by omega : i.val ≤ n) ⟨p.val, h⟩).castSucc
        else Fin.last n := by sorry
