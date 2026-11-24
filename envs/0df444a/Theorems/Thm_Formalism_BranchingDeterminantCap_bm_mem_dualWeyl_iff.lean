-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_mem_dualWeyl_iff
-- name    : Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:30.073193+00:00
-- url     : https://prove2.me/theorems/dd424354-c2f0-4249-8d69-055505d827b4
-- title:
--   Branching Determinant Cap: bm mem dual Weyl iff
-- statement:
--   The Branching Determinant Cap construction uses the bm mem dual Weyl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L966-L987
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L966-L987

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

theorem Formalism.BranchingDeterminantCap.bm_mem_dualWeyl_iff {R : Type} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ} {ν : Fin n → ℕ}
    {G : MvPolynomial (Fin r × Fin n) R} :
    G ∈ dualWeyl R r n ν ↔
      (∀ s, ndEul R r n s G = (ν s : R) • G) ∧ ∀ l j : Fin n, l < j → ndE R r n l j G = 0 := by sorry
