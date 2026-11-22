-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_le_node
-- name    : DeciSigma1.Satisfiability.leastShape_le_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:54.047824+00:00
-- url     : https://prove2.me/theorems/514667db-e1cb-4061-861f-0f2dc8d5ce34
-- title:
--   Satisfiability: least Shape le node
-- statement:
--   The least shape satisfies the upper constructor bounds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L250-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L250-L264

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.leastShape_le_node {x : V} {b : Fin n → V} (hl : LitT.leF x b ∈ Γ) :
    leastShape Γ x ≤ Semantics.Tree.node (leastShape Γ ∘ b) := by sorry
