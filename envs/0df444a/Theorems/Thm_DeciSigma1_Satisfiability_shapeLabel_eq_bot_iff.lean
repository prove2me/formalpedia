-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_eq_bot_iff
-- name    : DeciSigma1.Satisfiability.shapeLabel_eq_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:49.407024+00:00
-- url     : https://prove2.me/theorems/80f105ca-f74d-4975-b8f6-b52296d28960
-- title:
--   Satisfiability: shape Label eq bot iff
-- statement:
--   The Satisfiability construction uses the shape Label eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L138-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L138-L143

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.shapeLabel_eq_bot_iff {π : List (Fin n)} {x : V} :
    shapeLabel Γ x π = .bot ↔ ¬ LowerLabel Γ π .f x ∧
      (UpperLabel Γ π .bot x ∨ UpperLabel Γ π .f x) := by sorry
