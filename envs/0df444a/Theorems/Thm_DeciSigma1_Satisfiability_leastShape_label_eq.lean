-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_label_eq
-- name    : DeciSigma1.Satisfiability.leastShape_label_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:22:07.974833+00:00
-- url     : https://prove2.me/theorems/5df1d3a7-70f6-42e0-981a-2858e0efa98c
-- title:
--   Satisfiability: least Shape label eq
-- statement:
--   The Satisfiability construction uses the least Shape label eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L199-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L199-L205

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.leastShape_label_eq {π : List (Fin n)} {x : V} {a : Semantics.Sym}
    (h : (leastShape Γ x).fn π = some a) : a = shapeLabel Γ x π := by sorry
