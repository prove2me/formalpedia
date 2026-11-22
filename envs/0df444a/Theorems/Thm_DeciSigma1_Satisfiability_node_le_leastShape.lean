-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_node_le_leastShape
-- name    : DeciSigma1.Satisfiability.node_le_leastShape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:28:46.30467+00:00
-- url     : https://prove2.me/theorems/b32909b8-8746-4632-ba7f-6b616f4420b1
-- title:
--   Satisfiability: node le least Shape
-- statement:
--   The least shape satisfies the lower constructor bounds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L233-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L233-L247

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.node_le_leastShape {a : Fin n → V} {x : V} (hl : LitT.fLe a x ∈ Γ) :
    Semantics.Tree.node (leastShape Γ ∘ a) ≤ leastShape Γ x := by sorry
