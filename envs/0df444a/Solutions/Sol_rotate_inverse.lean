-- Prove2me | solution 1 for rotate_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:15.19504+00:00
-- url     : https://prove2.me/submissions/dcef872e-ae60-43ff-817d-da07eee77b8c

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
theorem _root_.solution (rho : RotationSystem d V) :
    (rotate d G hG rho).symm = rotate d G hG (inverseRotationSystem d rho) := by
  apply Equiv.ext
  rintro ⟨v,x⟩
  apply Dart.ext
  · rfl
  · change ((localRotation d G hG (rho v) v).symm x).1 =
      (localRotation d G hG (negOffset d (rho v)) v x).1
    rw [localRotation_neg]
