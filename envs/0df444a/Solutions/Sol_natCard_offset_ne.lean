-- Prove2me | solution 1 for natCard_offset_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:06:57.030937+00:00
-- url     : https://prove2.me/submissions/95f5aaff-2e41-408f-82b9-6cb188365798

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_offset

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
theorem _root_.solution (a : Offset d) :
    Nat.card {b : Offset d // b ≠ a} = d - 2 := by
  classical
  let : Fintype {b : Offset d // b ≠ a} := Fintype.ofFinite _
  let : Fintype {b : Offset d // b = a} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun b : Offset d ↦ b = a)]
  rw [card_offset]
  simp only [Fintype.card_subtype_eq]
  have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  omega
