-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_fixed
-- name    : DeciSigma1.Semantics.SignSelection.select_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:58.438011+00:00
-- url     : https://prove2.me/theorems/171c16bd-9e61-425e-b157-ed8ad341d030
-- title:
--   Sign Selection: select fixed
-- statement:
--   The selected assignment is fixed by sign duality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L279-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L279-L285

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

theorem DeciSigma1.Semantics.SignSelection.select_fixed (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) : dual (select c B h) = select c B h := by sorry
