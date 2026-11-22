-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Closure_decompStep_iff
-- name    : DeciSigma1.Constraints.Closure.decompStep_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:24:59.854991+00:00
-- url     : https://prove2.me/theorems/f61bd4e8-0dbf-45b7-880f-850936c428a2
-- title:
--   Closure: decomp Step iff
-- statement:
--   The Closure construction uses the decomp Step iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L235-L245
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L235-L245

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
open DeciSigma1.Constraints.Closure
omit [Fintype V] [DecidableEq V]

theorem DeciSigma1.Constraints.Closure.decompStep_iff (Γ : List (LitT n V)) (s : Finset (V × V)) (x y : V) :
    DecompStep Γ s x y ↔
      ∃ a u v b i, LitT.fLe a u ∈ Γ ∧ (u, v) ∈ s ∧ LitT.leF v b ∈ Γ ∧
        a i = x ∧ b i = y := by sorry
