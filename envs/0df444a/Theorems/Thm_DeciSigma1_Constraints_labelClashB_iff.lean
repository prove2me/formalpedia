-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_labelClashB_iff
-- name    : DeciSigma1.Constraints.labelClashB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:26:49.577695+00:00
-- url     : https://prove2.me/theorems/1985576d-a26c-42a6-8cd7-00bbfa977ec9
-- title:
--   Constraints: label Clash B iff
-- statement:
--   The Constraints construction uses the label Clash B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L364-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L364-L366

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
variable [Fintype V] [DecidableEq V]

theorem DeciSigma1.Constraints.labelClashB_iff (Γ : List (LitT n V)) : labelClashB Γ = true ↔ LabelClash Γ := by sorry
