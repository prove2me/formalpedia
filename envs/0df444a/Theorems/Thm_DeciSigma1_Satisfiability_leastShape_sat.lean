-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_sat
-- name    : DeciSigma1.Satisfiability.leastShape_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:08.373122+00:00
-- url     : https://prove2.me/theorems/44ab1907-1c7d-4b63-a63b-4182f13f68cf
-- title:
--   Satisfiability: least Shape sat
-- statement:
--   The least shape solves every constraint without label clash.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L285-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L285-L292

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.leastShape_sat (hn : ¬ LabelClash Γ) : Covariant.Sat (leastShape Γ) Γ := by sorry
