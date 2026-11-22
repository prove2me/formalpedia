-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
-- name    : DeciSigma1.Holes.Tail.NoSuffixOccurrenceEndsBetween.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:16.506611+00:00
-- url     : https://prove2.me/theorems/cffcad90-d1e1-4088-98a7-3e78e7173e7a
-- title:
--   No Suffix Occurrence Ends Between: mono
-- statement:
--   The No Suffix Occurrence Ends Between construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L157-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L157-L160

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
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.NoSuffixOccurrenceEndsBetween.mono [DecidableEq α] {x t : List α} {b B c c' : ℕ}
    (h : NoSuffixOccurrenceEndsBetween x t b c c')
    (hb : b ≤ B) : NoSuffixOccurrenceEndsBetween x t B c c' := by sorry
