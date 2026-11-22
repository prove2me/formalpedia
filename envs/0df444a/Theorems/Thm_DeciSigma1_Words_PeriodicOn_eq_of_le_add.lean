-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_le_add
-- name    : DeciSigma1.Words.PeriodicOn.eq_of_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:39.326408+00:00
-- url     : https://prove2.me/theorems/5bf57e94-8528-4b44-ad7b-cf49f6828f89
-- title:
--   Periodic On: eq of le add
-- statement:
--   In a periodic interval, positions that differ by a multiple of the period carry equal
--   letters.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L158-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L158-L167

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

theorem DeciSigma1.Words.PeriodicOn.eq_of_le_add (h : PeriodicOn w d s e) {p : ℕ} (hp : s ≤ p) :
    ∀ j, p + j * d < e → w[p]? = w[p + j * d]? := by sorry
