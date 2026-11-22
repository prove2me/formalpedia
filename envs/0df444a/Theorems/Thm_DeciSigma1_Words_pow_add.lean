-- Prove2me | Theorems.Thm_DeciSigma1_Words_pow_add
-- name    : DeciSigma1.Words.pow_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:52.840512+00:00
-- url     : https://prove2.me/theorems/1f3faf6f-6be8-4170-9e48-f34c8004fc9c
-- title:
--   Words: pow add
-- statement:
--   The Words construction uses the pow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L56-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L56-L59

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
variable {μ π u w : List α} {p q n : ℕ}

theorem DeciSigma1.Words.pow_add (μ : List α) (m n : ℕ) : pow μ (m + n) = pow μ m ++ pow μ n := by sorry
