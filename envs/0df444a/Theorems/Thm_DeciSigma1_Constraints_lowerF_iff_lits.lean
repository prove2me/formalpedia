-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_lowerF_iff_lits
-- name    : DeciSigma1.Constraints.lowerF_iff_lits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:25:41.686382+00:00
-- url     : https://prove2.me/theorems/2a4629cf-81d5-465f-967c-e28109b49550
-- title:
--   Constraints: lower F iff lits
-- statement:
--   The Constraints construction uses the lower F iff lits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L328-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L328-L334

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.lowerF_iff_lits (Γ : List (LitT n V)) (x : V) :
    LowerF Γ x ↔ ∃ l ∈ lowerLits Γ, Derives Γ l.2 x := by sorry
