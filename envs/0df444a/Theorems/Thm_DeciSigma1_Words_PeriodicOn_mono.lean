-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
-- name    : DeciSigma1.Words.PeriodicOn.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:19.343174+00:00
-- url     : https://prove2.me/theorems/e4b4bdb0-f6d2-4492-b428-45292feb4e91
-- title:
--   Periodic On: mono
-- statement:
--   The Periodic On construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L152-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L152-L154

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
open DeciSigma1.Words.PeriodicOn
variable {w : List α} {d s e : ℕ}

theorem DeciSigma1.Words.PeriodicOn.mono {s' e' : ℕ} (h : PeriodicOn w d s e) (hs : s ≤ s') (he : e' ≤ e) :
    PeriodicOn w d s' e' := by sorry
