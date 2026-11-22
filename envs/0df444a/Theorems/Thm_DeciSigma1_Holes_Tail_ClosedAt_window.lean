-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_ClosedAt_window
-- name    : DeciSigma1.Holes.Tail.ClosedAt.window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:06.239153+00:00
-- url     : https://prove2.me/theorems/f2098a7b-fa1a-414d-9ee4-5f7a3ba7ec64
-- title:
--   Closed At: window
-- statement:
--   The Closed At construction uses the window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L586-L591
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L586-L591

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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}

theorem DeciSigma1.Holes.Tail.ClosedAt.window (hcl : ClosedAt T q0 x B c c') {j : ℕ} (hj : j < B) :
    x[c - B + j]? = x[c' - B + j]? := by sorry
