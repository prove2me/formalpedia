-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_commute_weightedComponent_of_monomial
-- name    : Formalism.BranchingDeterminantCap.commute_weightedComponent_of_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:45.13579+00:00
-- url     : https://prove2.me/theorems/d3e83fe9-e9b8-4c8c-a08a-77c07074824b
-- title:
--   Branching Determinant Cap: commute weighted Component of monomial
-- statement:
--   The Branching Determinant Cap construction uses the commute weighted Component of monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L197-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L197-L216

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

theorem Formalism.BranchingDeterminantCap.commute_weightedComponent_of_monomial {R σ B : Type*} [CommRing R] [AddCommMonoid B] [IsRightCancelAdd B] (w : σ → B)
    (D : Module.End R (MvPolynomial σ R))
    (hD : ∀ m, IsWeightedHomogeneous w (D (monomial m 1)) (Finsupp.weight w m)) (β : B) :
    Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) D := by sorry
