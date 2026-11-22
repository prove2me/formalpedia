-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_UpperAt_le_embed
-- name    : DeciSigma1.Constraints.UpperAt.le_embed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:37.815346+00:00
-- url     : https://prove2.me/theorems/83717075-e642-420b-8d6f-e6f1bab6fc2c
-- title:
--   Upper At: le embed
-- statement:
--   The Upper At construction uses the le embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L527-L539
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L527-L539

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
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Constraints.UpperAt.le_embed {π : List (Fin n)} {x y : V}
    (h : UpperAt Γ π x y) {ρ : V → Semantics.Tree n} (hρ : Covariant.Sat ρ Γ) :
    ρ x ≤ PathBounds.embed Tree.top π (ρ y) := by sorry
