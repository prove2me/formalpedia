-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_restrict_sat
-- name    : DeciSigma1.Constraints.Ranked.Extension.restrict_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:05.68897+00:00
-- url     : https://prove2.me/theorems/3a544fed-7a9e-4135-bcee-203a95a10b2e
-- title:
--   Extension: restrict sat
-- statement:
--   A solution of an extension, restricted to the original variables, solves the original
--   constraint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L309-L313
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L309-L313

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.Ranked
open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}

theorem DeciSigma1.Constraints.Ranked.Extension.restrict_sat (e : Extension Γ ψ Source Sink rank)
    {ρ' : Fin (k + m) → Semantics.Tree n} (h : Covariant.Sat ρ' ψ) : Covariant.Sat
        (ρ' ∘ Fin.castAdd m) Γ := by sorry
