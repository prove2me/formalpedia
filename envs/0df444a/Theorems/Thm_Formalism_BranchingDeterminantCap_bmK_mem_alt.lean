-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_mem_alt
-- name    : Formalism.BranchingDeterminantCap.bmK_mem_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:00.453786+00:00
-- url     : https://prove2.me/theorems/384a3003-cf3d-4e7b-9886-f4f958992522
-- title:
--   Branching Determinant Cap: bm K mem alt
-- statement:
--   The Branching Determinant Cap construction uses the bm K mem alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2460-L2462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2460-L2462

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

theorem Formalism.BranchingDeterminantCap.bmK_mem_alt {R : Type*} [CommRing R] {n : ℕ} {lam : Fin n → ℕ} {d : ℕ} {G : BP R n} :
    G ∈ bmW R n lam d ↔ G ∈ dualWeyl R (n + 1) n lam ∧ IsWeightedHomogeneous (lastW n) G d := by sorry
