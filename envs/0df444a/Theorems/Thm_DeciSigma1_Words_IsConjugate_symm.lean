-- Prove2me | Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
-- name    : DeciSigma1.Words.IsConjugate.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:02.847129+00:00
-- url     : https://prove2.me/theorems/4c00b66c-2cfd-4682-9633-cc129f7ce255
-- title:
--   Is Conjugate: symm
-- statement:
--   The Is Conjugate construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L387-L388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L387-L388

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

theorem DeciSigma1.Words.IsConjugate.symm (h : IsConjugate ρ ρ') : IsConjugate ρ' ρ := by sorry
