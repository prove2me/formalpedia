-- Prove2me | solution 1 for sum_returnLength_le_d_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:46.657674+00:00
-- url     : https://prove2.me/submissions/91d8c3e1-6b66-4923-b438-251819a91661

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_dart
public import Theorems.Thm_validReturnBases_injective
public import Theorems.Thm_MiniFirstReturn_sum_time_le_card

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
theorem _root_.solution (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    ∑ q : ValidDeviation d G hG start rho.1 k,
      returnLength d G hG start rho.1 k q ≤ d * Fintype.card V := by
  calc
    ∑ q : ValidDeviation d G hG start rho.1 k,
        returnLength d G hG start rho.1 k q ≤ Fintype.card (Dart G) :=
      (by
        simpa only [returnLength] using
          (MiniFirstReturn.sum_time_le_card
            (Dart.phi d G hG rho.1)
            (pathIncomingDarts d G hG start rho.1 k)
            (validReturnBases d G hG start rho.1 k)
            (validReturnBases_injective d G hG start rho)))
    _ = d * Fintype.card V := by
      rw [← Nat.card_eq_fintype_card, natCard_dart d G hG]
