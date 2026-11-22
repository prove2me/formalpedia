-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicFrom_add_mul
-- name    : DeciSigma1.Words.PeriodicFrom.add_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:41.506401+00:00
-- url     : https://prove2.me/theorems/ffb1b363-869d-423f-9d2c-94b85af95ea2
-- title:
--   Periodic From: add mul
-- statement:
--   The Periodic From construction uses the add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L205-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L205-L214

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
variable {α : Type}

theorem DeciSigma1.Words.PeriodicFrom.add_mul {ξ : ℕ → α} {A p : ℕ} (h : PeriodicFrom ξ A p) (s m : ℕ) :
    ξ (A + s + m * p) = ξ (A + s) := by sorry
