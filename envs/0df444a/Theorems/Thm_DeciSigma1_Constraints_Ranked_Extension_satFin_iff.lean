-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_satFin_iff
-- name    : DeciSigma1.Constraints.Ranked.Extension.satFin_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:31.889606+00:00
-- url     : https://prove2.me/theorems/c32e4871-93fe-4c5d-934f-b66a9041611f
-- title:
--   Extension: sat Fin iff
-- statement:
--   A ranked extension has a finite solution exactly when it has a solution and the original
--   constraint has a finite solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L327-L336
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L327-L336

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.Ranked
open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}

theorem DeciSigma1.Constraints.Ranked.Extension.satFin_iff (e : Extension Γ ψ Source Sink rank) :
    (∃ σ : Fin (k + m) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ) ↔
      (∃ ρ', Covariant.Sat ρ' ψ) ∧ ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by sorry
