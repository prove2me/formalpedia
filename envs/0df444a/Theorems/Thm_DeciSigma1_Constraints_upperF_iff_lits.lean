-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_upperF_iff_lits
-- name    : DeciSigma1.Constraints.upperF_iff_lits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:25:48.104896+00:00
-- url     : https://prove2.me/theorems/b6a0d924-3984-48a8-a865-afb16beee90c
-- title:
--   Constraints: upper F iff lits
-- statement:
--   The Constraints construction uses the upper F iff lits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L336-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L336-L342

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

theorem DeciSigma1.Constraints.upperF_iff_lits (Γ : List (LitT n V)) (x : V) :
    UpperF Γ x ↔ ∃ m ∈ upperLits Γ, Derives Γ x m.1 := by sorry
