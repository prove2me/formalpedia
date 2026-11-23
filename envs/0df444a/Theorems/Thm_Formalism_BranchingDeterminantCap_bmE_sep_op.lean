-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_sep_op
-- name    : Formalism.BranchingDeterminantCap.bmE_sep_op
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:42.497211+00:00
-- url     : https://prove2.me/theorems/046826b0-c9bb-4156-82b4-b20de13cc4bc
-- title:
--   Branching Determinant Cap: bm E sep op
-- statement:
--   The Branching Determinant Cap construction uses the bm E sep op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1102-L1180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1102-L1180

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

theorem Formalism.BranchingDeterminantCap.bmE_sep_op {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (ω : B → ℤ)
    (C : ℤ → Module.End R (MvPolynomial σ R)) (W : Submodule R (MvPolynomial σ R)) (χ : B → ℤ → ℤ)
    (admitted : B → Prop) (hCC : ∀ u v, Commute (C u) (C v))
    (hCc : ∀ u β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) (C u))
    (hCW : ∀ u, ∀ G ∈ W, C u G ∈ W)
    (hEig : ∀ G ∈ W, ∀ β, weightedHomogeneousComponent w β G ≠ 0 →
      (∀ β', weightedHomogeneousComponent w β' G ≠ 0 → ω β' ≤ ω β) →
      admitted β ∧ ∀ u, C u (weightedHomogeneousComponent w β G) =
        ((χ β u : ℤ) : R) • weightedHomogeneousComponent w β G)
    (hSep : ∀ β β', admitted β → admitted β' → β ≠ β' → ∃ u, χ β u ≠ χ β' u) :
    ∀ (k : ℕ) (S : Finset B) (β0 : B), S.card ≤ k → admitted β0 → β0 ∉ S →
      ∃ (Q : Module.End R (MvPolynomial σ R)) (q : ℤ), q ≠ 0 ∧ (∀ u, Commute Q (C u)) ∧
        (∀ β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) Q) ∧
        (∀ G ∈ W, Q G ∈ W) ∧
        (∀ F, (∀ u, C u F = ((χ β0 u : ℤ) : R) • F) → Q F = ((q : ℤ) : R) • F) ∧
        (∀ G ∈ W, (∀ β, weightedHomogeneousComponent w β G ≠ 0 → β ∈ S) → Q G = 0) := by sorry
