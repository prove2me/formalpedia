-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_ClosedAt_nodeClosedAt
-- name    : DeciSigma1.Holes.Tail.ClosedAt.nodeClosedAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:11.768972+00:00
-- url     : https://prove2.me/theorems/16545243-77f3-4a1b-be50-927dbb6ca83a
-- title:
--   Closed At: node Closed At
-- statement:
--   A factor closed at window `B` is closed for every dictionary of words of length at most `B`
--   that contains the empty word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L439-L451
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L439-L451

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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}

theorem DeciSigma1.Holes.Tail.ClosedAt.nodeClosedAt (hcl : ClosedAt T q0 x B c c') (hD : [] ∈ D)
    (hB : ∀ r ∈ D, r.length ≤ B) : NodeClosedAt T q0 D x c c' := by sorry
