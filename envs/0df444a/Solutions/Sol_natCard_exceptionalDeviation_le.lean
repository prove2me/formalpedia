-- Prove2me | solution 1 for natCard_exceptionalDeviation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:20.299815+00:00
-- url     : https://prove2.me/submissions/d8551d16-462f-4f78-a776-9004d023dc9b

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_natCard_exceptionalDart_le
public import Theorems.Thm_exceptionalDeviationToDart_injective

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
    Nat.card (ExceptionalDeviation d G hG start rho) ≤ 4 * d :=
  (Nat.card_le_card_of_injective _
    (exceptionalDeviationToDart_injective d G hG start rho)).trans
      (natCard_exceptionalDart_le d G hG start rho.1 k)
