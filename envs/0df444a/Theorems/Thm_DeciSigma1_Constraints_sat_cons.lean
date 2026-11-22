-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sat_cons
-- name    : DeciSigma1.Constraints.sat_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:35.549803+00:00
-- url     : https://prove2.me/theorems/a706483c-0d95-4112-a1ce-d021a03088c1
-- title:
--   Constraints: sat cons
-- statement:
--   The Constraints construction uses the sat cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L56-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L56-L58

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n k m : ℕ}
variable {V : Type*}

theorem DeciSigma1.Constraints.sat_cons (ρ : V → Semantics.Tree n) (l : LitT n V) (Γ : List (LitT n V)) :
    Covariant.Sat ρ (l :: Γ) ↔ Covariant.Holds ρ l ∧ Covariant.Sat ρ Γ := by sorry
