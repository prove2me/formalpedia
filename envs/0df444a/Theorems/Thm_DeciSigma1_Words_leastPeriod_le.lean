-- Prove2me | Theorems.Thm_DeciSigma1_Words_leastPeriod_le
-- name    : DeciSigma1.Words.leastPeriod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:01.699546+00:00
-- url     : https://prove2.me/theorems/4c592d17-1cba-4531-9c83-2babcfccef67
-- title:
--   Words: least Period le
-- statement:
--   The Words construction uses the least Period le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L121-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L121-L122

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
variable [DecidableEq α] {w : List α} {p g : ℕ}

theorem DeciSigma1.Words.leastPeriod_le (hp : 0 < p) (h : w.HasPeriod p) : leastPeriod w ≤ p := by sorry
