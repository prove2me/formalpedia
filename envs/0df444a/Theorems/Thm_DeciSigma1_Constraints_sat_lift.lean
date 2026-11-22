-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_sat_lift
-- name    : DeciSigma1.Constraints.sat_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:33.763856+00:00
-- url     : https://prove2.me/theorems/5b163ad8-cd45-4ce6-962e-b8e9298e385f
-- title:
--   Constraints: sat lift
-- statement:
--   The Constraints construction uses the sat lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L46-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L46-L48

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n k m : ℕ}

theorem DeciSigma1.Constraints.sat_lift (ρ' : Fin (k + m) → Semantics.Tree n) (Γ : List (LitT n (Fin k))) :
    Covariant.Sat ρ' (lift Γ m) ↔ Covariant.Sat (ρ' ∘ Fin.castAdd m) Γ := by sorry
