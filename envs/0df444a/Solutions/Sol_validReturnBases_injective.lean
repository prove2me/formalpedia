-- Prove2me | solution 1 for validReturnBases_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:10.016802+00:00
-- url     : https://prove2.me/submissions/8545e045-18d1-4b18-9023-a6a23acd0809

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
theorem _root_.solution (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective (validReturnBases d G hG start rho.1 k) := by
  rintro ⟨⟨i,a⟩, ha⟩ ⟨⟨j,b⟩, hbvalid⟩ hqq
  have hb : returnBase d G hG start rho.1 (i,a) =
      returnBase d G hG start rho.1 (j,b) := congrArg Subtype.val hqq
  have hv : orbitVertex d G hG start rho.1 (internalTime i) =
      orbitVertex d G hG start rho.1 (internalTime j) := by
    simpa using congrArg (Dart.head G) hb
  have hiFin :
      (⟨internalTime i,
        lt_trans (internalTime_lt i) (Nat.lt_succ_self k)⟩ : Fin (k + 1)) =
      ⟨internalTime j,
        lt_trans (internalTime_lt j) (Nat.lt_succ_self k)⟩ := rho.2 hv
  have hi : i = j := by
    apply Fin.ext
    simpa [internalTime] using congrArg Fin.val hiFin
  subst j
  have hs : sideDart d G hG start rho.1 (i,a) =
      sideDart d G hG start rho.1 (i,b) := by
    exact (Dart.phi d G hG rho.1).symm.injective hb
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact sideDart_injective_offset d G hG start rho.1 i hs
