-- Prove2me | Theorems.Thm_DeciSigma1_Words_leastPeriod_pos
-- name    : DeciSigma1.Words.leastPeriod_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:56.559268+00:00
-- url     : https://prove2.me/theorems/67599f98-5637-49e0-a4fb-d5fab07ca7b6
-- title:
--   Words: least Period pos
-- statement:
--   The Words construction uses the least Period pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L115-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L115-L116

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

theorem DeciSigma1.Words.leastPeriod_pos (w : List α) : 0 < leastPeriod w := by sorry
