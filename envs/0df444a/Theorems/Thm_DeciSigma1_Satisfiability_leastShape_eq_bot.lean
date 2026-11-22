-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_eq_bot
-- name    : DeciSigma1.Satisfiability.leastShape_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:50.10617+00:00
-- url     : https://prove2.me/theorems/0522d19f-6cb5-4339-a1c6-45b6476d6b92
-- title:
--   Satisfiability: least Shape eq bot
-- statement:
--   A variable fixed to `⊥` is `⊥` in the least shape.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L210-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L210-L218

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.leastShape_eq_bot (hn : ¬ LabelClash Γ) {x : V}
    (hl : LitT.eqBot x ∈ Γ) : leastShape Γ x = Tree.bot := by sorry
