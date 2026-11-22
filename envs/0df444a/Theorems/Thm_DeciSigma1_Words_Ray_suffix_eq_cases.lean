-- Prove2me | Theorems.Thm_DeciSigma1_Words_Ray_suffix_eq_cases
-- name    : DeciSigma1.Words.Ray.suffix_eq_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:56.740859+00:00
-- url     : https://prove2.me/theorems/20fe89ab-3e38-4459-bf4e-2675c91907c8
-- title:
--   Ray: suffix eq cases
-- statement:
--   If two suffixes of rays are equal, either both start at or after the onsets, or both start
--   before them at the same distance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L490-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Basic.lean#L490-L517

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

theorem DeciSigma1.Words.Ray.suffix_eq_cases {Ω' : Ray α} {a b : ℕ} (h : ∀ t, Ω.stream (a + t) = Ω'.stream (b + t)) :
    (Ω.onset ≤ a ∧ Ω'.onset ≤ b) ∨ (a < Ω.onset ∧ Ω.onset - a = Ω'.onset - b) := by sorry
