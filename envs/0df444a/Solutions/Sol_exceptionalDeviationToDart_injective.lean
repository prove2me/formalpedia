-- Prove2me | solution 1 for exceptionalDeviationToDart_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:38.547672+00:00
-- url     : https://prove2.me/submissions/247181d2-f849-4c4d-adf7-4b10407da59c

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_returnEndpoint_injective

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
    Function.Injective (exceptionalDeviationToDart d G hG start rho) := by
  intro q q' h
  apply Subtype.ext
  apply returnEndpoint_injective d G hG start rho
  exact congrArg
    (fun e : ExceptionalDart d G hG start rho.1 k ↦ (e.1 : Dart G)) h
