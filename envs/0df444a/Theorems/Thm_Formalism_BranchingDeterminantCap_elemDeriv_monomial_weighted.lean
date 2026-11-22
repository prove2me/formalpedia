-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_monomial_weighted
-- name    : Formalism.BranchingDeterminantCap.elemDeriv_monomial_weighted
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:04.633513+00:00
-- url     : https://prove2.me/theorems/a04221d4-0aba-4395-8165-ccfbaff98909
-- title:
--   Branching Determinant Cap: elem Deriv monomial weighted
-- statement:
--   The Branching Determinant Cap construction uses the elem Deriv monomial weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L218-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L218-L235

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

theorem Formalism.BranchingDeterminantCap.elemDeriv_monomial_weighted (R : Type*) [CommRing R] (n : ℕ) {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ (a : Fin (n + 1)) (s t : Fin n), a ≠ Fin.last n → w (a, s) = w (a, t))
    (s t : Fin n) (m : Fin (n + 1) × Fin n →₀ ℕ) :
    IsWeightedHomogeneous w (bmEL R n s t (monomial m 1)) (Finsupp.weight w m) := by sorry
