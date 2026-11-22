-- Prove2me | Theorems.Thm_DeciSigma1_Words_IsConjugate_length_eq
-- name    : DeciSigma1.Words.IsConjugate.length_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:08.816776+00:00
-- url     : https://prove2.me/theorems/e930f14f-5999-45a8-83a2-870a64c4b338
-- title:
--   Is Conjugate: length eq
-- statement:
--   The Is Conjugate construction uses the length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L394-L395
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L394-L395

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
open DeciSigma1.Words.IsConjugate
variable {ρ ρ' ρ'' : List α}

theorem DeciSigma1.Words.IsConjugate.length_eq (h : IsConjugate ρ ρ') : ρ'.length = ρ.length := by sorry
