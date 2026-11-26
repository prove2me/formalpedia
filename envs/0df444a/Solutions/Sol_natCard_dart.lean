-- Prove2me | solution 1 for natCard_dart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:59.10291+00:00
-- url     : https://prove2.me/submissions/b680afe8-5038-414a-bfe5-42ad58fe3f23

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

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
include hG
theorem _root_.solution : Nat.card (Dart G) = d * Fintype.card V := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [show ∀ v : V, Fintype.card (G.neighborSet v) = d by
    intro v
    rw [← Nat.card_eq_fintype_card]
    exact hG v]
  simp [mul_comm]
