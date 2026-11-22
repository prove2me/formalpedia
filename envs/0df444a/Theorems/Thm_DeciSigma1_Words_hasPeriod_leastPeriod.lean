-- Prove2me | Theorems.Thm_DeciSigma1_Words_hasPeriod_leastPeriod
-- name    : DeciSigma1.Words.hasPeriod_leastPeriod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:12.788801+00:00
-- url     : https://prove2.me/theorems/b64bf153-ea7e-49e3-a736-4a9e0829e192
-- title:
--   Words: has Period least Period
-- statement:
--   The Words construction uses the has Period least Period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L118-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L118-L119

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

theorem DeciSigma1.Words.hasPeriod_leastPeriod (w : List α) : w.HasPeriod (leastPeriod w) := by sorry
