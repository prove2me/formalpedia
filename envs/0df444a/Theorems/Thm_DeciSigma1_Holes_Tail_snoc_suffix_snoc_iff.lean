-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_snoc_suffix_snoc_iff
-- name    : DeciSigma1.Holes.Tail.snoc_suffix_snoc_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:12.447795+00:00
-- url     : https://prove2.me/theorems/78dbd095-b59a-4b74-a375-2a06676afb25
-- title:
--   Tail: snoc suffix snoc iff
-- statement:
--   Comparing suffixes after appending one letter to each word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L121-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L121-L129

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

theorem DeciSigma1.Holes.Tail.snoc_suffix_snoc_iff {u w : List α} {a b : α} :
    u ++ [b] <:+ w ++ [a] ↔ u <:+ w ∧ b = a := by sorry
