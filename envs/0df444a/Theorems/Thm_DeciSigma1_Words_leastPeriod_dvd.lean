-- Prove2me | Theorems.Thm_DeciSigma1_Words_leastPeriod_dvd
-- name    : DeciSigma1.Words.leastPeriod_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:46.847072+00:00
-- url     : https://prove2.me/theorems/0d05aa67-9afe-4e96-98fc-42ae94c265db
-- title:
--   Words: least Period dvd
-- statement:
--   The least period of a word of length at least `2g` with period `g` divides `g`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L125-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L125-L138

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

theorem DeciSigma1.Words.leastPeriod_dvd (h : w.HasPeriod g) (h2 : 2 * g ≤ w.length) : leastPeriod w ∣ g := by sorry
