-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_suffixDictionary_le
-- name    : DeciSigma1.Holes.Tail.card_suffixDictionary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:08:32.514404+00:00
-- url     : https://prove2.me/theorems/a63724bd-6cf2-4bfb-93ae-dfcb3dd9487d
-- title:
--   Tail: card suffix Dictionary le
-- statement:
--   The suffix dictionary of `m` targets at window `B` has at most `m B (B + 1) / 2 + 1`
--   words.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L254-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L254-L264

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
variable [DecidableEq α]
variable {ts : List (List α)} {B : ℕ}

theorem DeciSigma1.Holes.Tail.card_suffixDictionary_le (ts : List (List α)) (B : ℕ) :
    (suffixDictionary ts B).card ≤ ts.length * (B * (B + 1) / 2) + 1 := by sorry
