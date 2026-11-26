-- Prove2me | solution 1 for natCard_exceptionalDart_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:42.247826+00:00
-- url     : https://prove2.me/submissions/ed6b071f-b74e-4954-a69b-7f5c0401c6b8

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_boundaryVertices_le_four
public import Theorems.Thm_exceptionalDartCode_injective

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
    (rho : RotationSystem d V) (k : ℕ) :
    Nat.card (ExceptionalDart d G hG start rho k) ≤ 4 * d := by
  calc
    Nat.card (ExceptionalDart d G hG start rho k) ≤
        Nat.card ({v : V // v ∈ boundaryVertices d G hG start rho k} × Fin d) :=
      Nat.card_le_card_of_injective _
        (exceptionalDartCode_injective d G hG start rho k)
    _ = (boundaryVertices d G hG start rho k).card * d := by simp
    _ ≤ 4 * d := Nat.mul_le_mul_right d
      (card_boundaryVertices_le_four d G hG start rho k)
