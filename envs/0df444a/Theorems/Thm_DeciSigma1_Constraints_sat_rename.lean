-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sat_rename
-- name    : DeciSigma1.Constraints.sat_rename
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:28.66917+00:00
-- url     : https://prove2.me/theorems/50dc93d5-5c8d-440c-8410-bbaae6396fde
-- title:
--   Constraints: sat rename
-- statement:
--   The Constraints construction uses the sat rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L139-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L139-L141

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

theorem DeciSigma1.Constraints.sat_rename {W : Type*} (r : V → W) (ρ : W → Semantics.Tree n) (Γ : List (LitT n V)) :
    Covariant.Sat ρ (Γ.map (LitT.map r)) ↔ Covariant.Sat (ρ ∘ r) Γ := by sorry
