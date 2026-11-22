-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod
-- name    : DeciSigma1.Words.PeriodicOn.eq_of_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:46.455545+00:00
-- url     : https://prove2.me/theorems/e3468a4b-7b32-4a30-a828-7e122fef3f00
-- title:
--   Periodic On: eq of mod
-- statement:
--   The Periodic On construction uses the eq of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L169-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L169-L179

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

theorem DeciSigma1.Words.PeriodicOn.eq_of_mod (h : PeriodicOn w d s e) {p q : ℕ} (hp : s ≤ p) (hq : s ≤ q) (hpe : p < e)
    (hqe : q < e) (hpq : p % d = q % d) : w[p]? = w[q]? := by sorry
