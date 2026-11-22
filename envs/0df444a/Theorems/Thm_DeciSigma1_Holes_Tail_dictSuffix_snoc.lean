-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_snoc
-- name    : DeciSigma1.Holes.Tail.dictSuffix_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:39.213973+00:00
-- url     : https://prove2.me/theorems/0105af14-f1d6-4d17-b580-837f9ed9f3f2
-- title:
--   Tail: dict Suffix snoc
-- statement:
--   If `D` contains the empty word and is closed under prefixes, the longest suffix in `D` after
--   one more letter `a` is the longest suffix in `D` of `dictSuffix D w ++ [a]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L319-L329
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L319-L329

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

theorem DeciSigma1.Holes.Tail.dictSuffix_snoc (hD : [] ∈ D) (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α)
    (a : α) : dictSuffix D (w ++ [a]) = dictSuffix D (dictSuffix D w ++ [a]) := by sorry
