-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_length_le_length_dictSuffix
-- name    : DeciSigma1.Holes.Tail.length_le_length_dictSuffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:07.017478+00:00
-- url     : https://prove2.me/theorems/3b2ade3a-47cf-4099-ad5d-22c8410e1156
-- title:
--   Tail: length le length dict Suffix
-- statement:
--   The Tail construction uses the length le length dict Suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L295-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L295-L304

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

theorem DeciSigma1.Holes.Tail.length_le_length_dictSuffix : ∀ {w s : List α}, s <:+ w → s ∈ D →
    s.length ≤ (dictSuffix D w).length
  := by sorry
