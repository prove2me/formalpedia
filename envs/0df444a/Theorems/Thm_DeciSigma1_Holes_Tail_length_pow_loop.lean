-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_length_pow_loop
-- name    : DeciSigma1.Holes.Tail.length_pow_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:20.696581+00:00
-- url     : https://prove2.me/theorems/3297ab10-4345-4384-964c-0d45655eb965
-- title:
--   Tail: length pow loop
-- statement:
--   The Tail construction uses the length pow loop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L509-L511
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L509-L511

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
variable {x : List α} {c c' L : ℕ}

theorem DeciSigma1.Holes.Tail.length_pow_loop (hc' : c' ≤ x.length) (n : ℕ) :
    (pow ((x.drop c).take (c' - c)) n).length = n * (c' - c) := by sorry
