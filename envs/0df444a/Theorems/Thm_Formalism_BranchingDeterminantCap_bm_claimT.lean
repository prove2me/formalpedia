-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_claimT
-- name    : Formalism.BranchingDeterminantCap.bm_claimT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:14.435183+00:00
-- url     : https://prove2.me/theorems/813badc6-1a60-46c2-a993-7a12b7b1e76e
-- title:
--   Branching Determinant Cap: bm claim T
-- statement:
--   The Branching Determinant Cap construction uses the bm claim T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1006-L1057
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1006-L1057

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

theorem Formalism.BranchingDeterminantCap.bm_claimT {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ) (H : BP R n)
    (hH : H ∈ dualWeyl R (n + 1) n lam)
    (hrow : ∀ m ∈ H.support, ∀ a : Fin n, rowDeg m a.castSucc = sg a)
    (hlow : IsLow (omg fun s => (lam s : ℤ) - (sg s : ℤ)) H) : H = 0 := by sorry
