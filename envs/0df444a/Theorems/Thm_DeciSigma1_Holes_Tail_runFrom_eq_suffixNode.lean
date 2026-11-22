-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_runFrom_eq_suffixNode
-- name    : DeciSigma1.Holes.Tail.runFrom_eq_suffixNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:42.560153+00:00
-- url     : https://prove2.me/theorems/ea372504-aab5-4573-a6ed-a026c39897ea
-- title:
--   Tail: run From eq suffix Node
-- statement:
--   The state after `w` is read from its suffix node.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L365-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L365-L368

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] {D : Finset (List α)}

theorem DeciSigma1.Holes.Tail.runFrom_eq_suffixNode (T : Table α S k) (q0 : S) (D : Finset (List α)) (w : List α) :
    runFrom T.step q0 w = runFrom T.step (suffixNode T q0 D w).2 (suffixNode T q0 D w).1 := by sorry
