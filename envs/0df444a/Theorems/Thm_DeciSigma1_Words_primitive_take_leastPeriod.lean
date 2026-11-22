-- Prove2me | Theorems.Thm_DeciSigma1_Words_primitive_take_leastPeriod
-- name    : DeciSigma1.Words.primitive_take_leastPeriod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:48.388109+00:00
-- url     : https://prove2.me/theorems/7181f9d7-3c8e-477d-a28c-3331cfdb6f4f
-- title:
--   Words: primitive take least Period
-- statement:
--   The prefix of length `leastPeriod w` of a word of length at least twice its least period is
--   primitive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L349-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L349-L368

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}

theorem DeciSigma1.Words.primitive_take_leastPeriod [DecidableEq α] {w : List α}
    (h2 : 2 * leastPeriod w ≤ w.length) : IsPrimitive (w.take (leastPeriod w)) := by sorry
