-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_sat
-- name    : DeciSigma1.Semantics.SignSelection.select_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:58.890958+00:00
-- url     : https://prove2.me/theorems/d34ab7cb-eb1e-440d-bf9f-19a877eff085
-- title:
--   Sign Selection: select sat
-- statement:
--   The selected assignment solves the signed translation whenever `B` does.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L367-L370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L367-L370

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

theorem DeciSigma1.Semantics.SignSelection.select_sat {c : Fin n → Bool} {Γ : List (LitT n V)} {B : (V × Bool) → Tree n}
    (hs : Covariant.Sat B (signed c Γ)) (h : ∀ z, SameShape (B z) (dual B z)) :
    Covariant.Sat (select c B h) (signed c Γ) := by sorry
