-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Closure_mem_expand
-- name    : DeciSigma1.Constraints.Closure.mem_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:32.859183+00:00
-- url     : https://prove2.me/theorems/d259710a-e7e4-4f4c-977b-f411996e26da
-- title:
--   Closure: mem expand
-- statement:
--   The Closure construction uses the mem expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L255-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L255-L262

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

theorem DeciSigma1.Constraints.Closure.mem_expand (Γ : List (LitT n V)) (s : Finset (V × V)) (x y : V) :
    (x, y) ∈ expand Γ s ↔
      (x, y) ∈ s ∨ x = y ∨ LitT.le x y ∈ Γ ∨
      (∃ z, (x, z) ∈ s ∧ (z, y) ∈ s) ∨
      (∃ a u v b i, LitT.fLe a u ∈ Γ ∧ (u, v) ∈ s ∧ LitT.leF v b ∈ Γ ∧
        a i = x ∧ b i = y) := by sorry
