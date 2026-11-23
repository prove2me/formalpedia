-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_kills
-- name    : Formalism.BranchingDeterminantCap.bm_list_kills
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:37.798149+00:00
-- url     : https://prove2.me/theorems/2bedd43e-0897-4041-9ad2-43321530e6f4
-- title:
--   Branching Determinant Cap: bm list kills
-- statement:
--   The Branching Determinant Cap construction uses the bm list kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1325-L1355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1325-L1355

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

theorem Formalism.BranchingDeterminantCap.bm_list_kills {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (β : Fin n → ℤ) (h : bmAdm lam (∑ s, (lam s - sg s)) β) (hne : β ≠ fun s => ((lam s - sg s : ℕ) : ℤ)) :
    ∃ u ∈ bmList lam sg, bmChi lam β u = 0 := by sorry
