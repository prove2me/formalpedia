-- Prove2me | solution 1 for natCard_validDeviation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:39.989174+00:00
-- url     : https://prove2.me/submissions/df096359-9b99-49ec-ba4d-053d9aa1959a

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_offset_ne

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
theorem _root_.solution (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) :
    Nat.card (ValidDeviation d G hG start rho k) = (k - 1) * (d - 2) := by
  classical
  rw [Nat.card_congr (validDeviationEquivSigma d G hG start rho k), Nat.card_sigma]
  simp_rw [natCard_offset_ne]
  simp
