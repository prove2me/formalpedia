-- Prove2me | Theorems.Thm_DeciSigma1_Words_leastPeriod_dvd_iff
-- name    : DeciSigma1.Words.leastPeriod_dvd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:39.454815+00:00
-- url     : https://prove2.me/theorems/019c46b8-bd41-43f1-a55d-5759ae6b25a7
-- title:
--   Words: least Period dvd iff
-- statement:
--   The periods of an infinite word are the multiples of its least positive period.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L173-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L173-L186

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type*}

theorem DeciSigma1.Words.leastPeriod_dvd_iff {ξ : ℕ → α} {p q : ℕ} (hp : LeastStreamPeriod ξ p) :
    StreamPeriod ξ q ↔ p ∣ q := by sorry
