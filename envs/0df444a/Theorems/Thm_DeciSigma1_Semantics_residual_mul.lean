-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_residual_mul
-- name    : DeciSigma1.Semantics.residual_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:48.237584+00:00
-- url     : https://prove2.me/theorems/7f9fea34-64d6-4859-9fa9-18d94a9e4797
-- title:
--   Semantics: residual mul
-- statement:
--   The residual of a concatenation by one letter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L107-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L107-L127

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}

theorem DeciSigma1.Semantics.residual_mul (A B : Language n) (c : Fin n) :
    residual (concat A B) [c] =
      concat (residual A [c]) B ∪
        {v | [] ∈ A ∧ c :: v ∈ B} := by sorry
