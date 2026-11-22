-- Prove2me | Theorems.Thm_DeciSigma1_Words_periodicOn_iff_hasPeriod
-- name    : DeciSigma1.Words.periodicOn_iff_hasPeriod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:49.323799+00:00
-- url     : https://prove2.me/theorems/747c7ed4-d310-4144-ae3e-30aa78f1c878
-- title:
--   Words: periodic On iff has Period
-- statement:
--   The Words construction uses the periodic On iff has Period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L216-L231
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L216-L231

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

theorem DeciSigma1.Words.periodicOn_iff_hasPeriod {w : List α} {d s e : ℕ} (hse : s ≤ e) (he : e ≤ w.length) :
    PeriodicOn w d s e ↔ ((w.drop s).take (e - s)).HasPeriod d := by sorry
