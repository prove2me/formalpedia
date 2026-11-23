-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_monomial_WH
-- name    : Formalism.BranchingDeterminantCap.bmF_rowAct_monomial_WH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:09.252415+00:00
-- url     : https://prove2.me/theorems/fe9e85f4-c550-4105-af9a-36e6891e0347
-- title:
--   Branching Determinant Cap: bm F row Act monomial WH
-- statement:
--   The Branching Determinant Cap construction uses the bm F row Act monomial WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1942-L1949
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1942-L1949

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

theorem Formalism.BranchingDeterminantCap.bmF_rowAct_monomial_WH (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (m : Fin (n + 1) × Fin n →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w (rowAct R (extM R g) (monomial m c : BP R n)) (Finsupp.weight w m) := by sorry
