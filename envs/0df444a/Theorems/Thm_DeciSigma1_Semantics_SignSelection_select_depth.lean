-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_depth
-- name    : DeciSigma1.Semantics.SignSelection.select_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:11.320056+00:00
-- url     : https://prove2.me/theorems/f3306fe7-24ac-43c1-a251-eec84890d83f
-- title:
--   Sign Selection: select depth
-- statement:
--   The selected assignment has bounded depth whenever `B` has.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L272-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L272-L276

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

theorem DeciSigma1.Semantics.SignSelection.select_depth (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) {D : ℕ}
    (hB : ∀ z π, ((B z).fn π).isSome → π.length ≤ D) (z : (V × Bool)) (π : List (Fin n))
    (hπ : ((select c B h z).fn π).isSome) : π.length ≤ D := by sorry
