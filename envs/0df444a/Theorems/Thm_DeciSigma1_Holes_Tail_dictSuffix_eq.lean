-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_eq
-- name    : DeciSigma1.Holes.Tail.dictSuffix_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:52.465634+00:00
-- url     : https://prove2.me/theorems/3e23c69a-d623-4c30-b4c9-715dce8d0ebf
-- title:
--   Tail: dict Suffix eq
-- statement:
--   A longest suffix of `w` in `D` is `dictSuffix D w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L311-L315
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L311-L315

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

theorem DeciSigma1.Holes.Tail.dictSuffix_eq (hD : [] ∈ D) {w s : List α} (hs : s <:+ w) (hsD : s ∈ D)
    (hmax : ∀ r, r <:+ w → r ∈ D → r.length ≤ s.length) : dictSuffix D w = s := by sorry
