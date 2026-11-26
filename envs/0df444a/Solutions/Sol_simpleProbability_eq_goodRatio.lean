-- Prove2me | solution 1 for simpleProbability_eq_goodRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:13:33.371897+00:00
-- url     : https://prove2.me/submissions/779d4800-4cad-4da3-9cb4-484f1cd1cfda

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_goodOmega
public import Theorems.Thm_card_walkCount
public import Theorems.Thm_card_rotationSystem_eq_free_mul_walkCount

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
theorem _root_.solution
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    simpleProbability G start k =
      (Nat.card (GoodOmega d G hG start k) : ℝ) /
        (Nat.card (RotationSystem d V) : ℝ) := by
  let free : ℕ := (d - 1) ^ (Fintype.card V - (k - 1))
  have hfree : 0 < free := by
    dsimp [free]
    exact pow_pos (by omega) _
  have hwalk : 0 < walkCount G start k := by
    rw [card_walkCount d G hG start k hk]
    exact pow_pos (by omega) _
  rw [simpleProbability, card_goodOmega d G hG start k hk,
    card_rotationSystem_eq_free_mul_walkCount d G hG start k hk hkn]
  change (simpleWalkCount G start k : ℝ) / (walkCount G start k : ℝ) =
    ((simpleWalkCount G start k * free : ℕ) : ℝ) /
      ((free * walkCount G start k : ℕ) : ℝ)
  push_cast
  field_simp [show (free : ℝ) ≠ 0 by exact_mod_cast hfree.ne',
    show (walkCount G start k : ℝ) ≠ 0 by exact_mod_cast hwalk.ne']
