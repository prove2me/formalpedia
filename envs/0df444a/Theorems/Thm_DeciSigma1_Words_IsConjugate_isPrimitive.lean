-- Prove2me | Theorems.Thm_DeciSigma1_Words_IsConjugate_isPrimitive
-- name    : DeciSigma1.Words.IsConjugate.isPrimitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:30.241448+00:00
-- url     : https://prove2.me/theorems/b83abd1a-d360-469f-a319-fe6a40d7ee0e
-- title:
--   Is Conjugate: is Primitive
-- statement:
--   The Is Conjugate construction uses the is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L397-L398
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L397-L398

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

theorem DeciSigma1.Words.IsConjugate.isPrimitive (h : IsConjugate ρ ρ') (hρ : IsPrimitive ρ) : IsPrimitive ρ' := by sorry
