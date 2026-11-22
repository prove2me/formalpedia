-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_eq_top
-- name    : DeciSigma1.Satisfiability.leastShape_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:48.336071+00:00
-- url     : https://prove2.me/theorems/5914f0cf-4962-48f2-a656-46e4c666131a
-- title:
--   Satisfiability: least Shape eq top
-- statement:
--   A variable fixed to `⊤` is `⊤` in the least shape.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L221-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L221-L230

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.leastShape_eq_top (hn : ¬ LabelClash Γ) {x : V}
    (hl : LitT.eqTop x ∈ Γ) : leastShape Γ x = Tree.top := by sorry
