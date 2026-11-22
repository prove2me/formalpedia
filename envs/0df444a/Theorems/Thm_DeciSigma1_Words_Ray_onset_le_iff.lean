-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_onset_le_iff
-- name    : DeciSigma1.Words.Ray.onset_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:54.455795+00:00
-- url     : https://prove2.me/theorems/40a4aa46-cbab-4e7a-9f61-2f76433c945d
-- title:
--   Ray: onset le iff
-- statement:
--   `onset ≤ A` if and only if the suffix from `A` is purely periodic.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L418-L420
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L418-L420

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
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
variable [DecidableEq α]

theorem DeciSigma1.Words.Ray.onset_le_iff {A : ℕ} : Ω.onset ≤ A ↔ ∃ p, 0 < p ∧ PeriodicFrom Ω.stream A p := by sorry
