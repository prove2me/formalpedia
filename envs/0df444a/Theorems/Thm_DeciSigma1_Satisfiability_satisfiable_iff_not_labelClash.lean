-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_satisfiable_iff_not_labelClash
-- name    : DeciSigma1.Satisfiability.satisfiable_iff_not_labelClash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:03.038163+00:00
-- url     : https://prove2.me/theorems/6b732a61-010e-4315-a1ec-ab2d9c598524
-- title:
--   Satisfiability: satisfiable iff not label Clash
-- statement:
--   A covariant constraint is satisfiable exactly when it has no label clash.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L295-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L295-L296

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.satisfiable_iff_not_labelClash : (∃ ρ, Covariant.Sat ρ Γ) ↔ ¬ LabelClash Γ := by sorry
