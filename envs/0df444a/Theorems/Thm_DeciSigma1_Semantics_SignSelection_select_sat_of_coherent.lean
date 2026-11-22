-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_sat_of_coherent
-- name    : DeciSigma1.Semantics.SignSelection.select_sat_of_coherent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:56.658101+00:00
-- url     : https://prove2.me/theorems/394627a5-d046-4fb3-a8e4-6f5c6de0c19f
-- title:
--   Sign Selection: select sat of coherent
-- statement:
--   The selected assignment solves every sign-coherent constraint that `B` and its sign dual
--   solve.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L289-L364
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L289-L364

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Semantics.SignSelection.select_sat_of_coherent {c : Fin n → Bool} {ψ : List (LitT n (V × Bool))}
    (hψ : SignCoherent c ψ) {B : (V × Bool) → Tree n} (hs : Covariant.Sat B ψ)
        (hS : Covariant.Sat (dual B) ψ)
    (h : ∀ z, SameShape (B z) (dual B z)) : Covariant.Sat (select c B h) ψ := by sorry
