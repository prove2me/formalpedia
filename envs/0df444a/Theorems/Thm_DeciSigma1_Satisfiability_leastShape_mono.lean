-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_mono
-- name    : DeciSigma1.Satisfiability.leastShape_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:54.487071+00:00
-- url     : https://prove2.me/theorems/8e1f5d10-706e-457b-aea5-a3efe5e8e467
-- title:
--   Satisfiability: least Shape mono
-- statement:
--   Derived inequalities are respected by the least shape.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L267-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L267-L282

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.leastShape_mono {x y : V} (h : Derives Γ x y) :
    leastShape Γ x ≤ leastShape Γ y := by sorry
