-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_mem
-- name    : DeciSigma1.Holes.Tail.dictSuffix_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:05.309806+00:00
-- url     : https://prove2.me/theorems/9d100544-47fc-4b84-9a13-7ef22ad7f31d
-- title:
--   Tail: dict Suffix mem
-- statement:
--   The Tail construction uses the dict Suffix mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L288-L293
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L288-L293

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

theorem DeciSigma1.Holes.Tail.dictSuffix_mem (hD : [] ∈ D) : ∀ w : List α, dictSuffix D w ∈ D
  := by sorry
