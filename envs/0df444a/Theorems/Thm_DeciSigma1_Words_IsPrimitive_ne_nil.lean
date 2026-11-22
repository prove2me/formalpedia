-- Prove2me | Theorems.Thm_DeciSigma1_Words_IsPrimitive_ne_nil
-- name    : DeciSigma1.Words.IsPrimitive.ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:25.792799+00:00
-- url     : https://prove2.me/theorems/bd078f14-9641-4acc-9c8c-1e4dac6ac581
-- title:
--   Is Primitive: ne nil
-- statement:
--   The Is Primitive construction uses the ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L319-L319
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L319-L319

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

theorem DeciSigma1.Words.IsPrimitive.ne_nil {ρ : List α} (h : IsPrimitive ρ) : ρ ≠ [] := by sorry
