-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_suffix_dictSuffix
-- name    : DeciSigma1.Holes.Tail.suffix_dictSuffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:59.342794+00:00
-- url     : https://prove2.me/theorems/265eb2a9-92d3-4f45-bd52-36d6d647704f
-- title:
--   Tail: suffix dict Suffix
-- statement:
--   Every suffix of `w` in `D` is a suffix of `dictSuffix D w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L307-L308
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L307-L308

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

theorem DeciSigma1.Holes.Tail.suffix_dictSuffix {w s : List α} (hs : s <:+ w) (hsD : s ∈ D) : s <:+ dictSuffix D w := by sorry
