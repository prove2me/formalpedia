-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Pinning_realize_bounds
-- name    : DeciSigma1.Full.Models.Pinning.realize_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:59:02.303149+00:00
-- url     : https://prove2.me/theorems/87d57fde-b72d-4d12-8baf-874457a4dcfb
-- title:
--   Pinning: realize bounds
-- statement:
--   Finitely many ground bounds that hold together in some solution of `Γ` hold together in a
--   finite solution, provided `Γ` has a finite solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L40-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean#L40-L69

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Pinning
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ}

theorem DeciSigma1.Full.Models.Pinning.realize_bounds {k : ℕ} (B : List (GroundBound n (Fin k))) (Γ : List (LitT n (Fin k)))
    (hf : ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ)
    (hs : ∃ ρ, Covariant.Sat ρ Γ ∧ ∀ b ∈ B, b.Holds ρ) :
    ∃ σ : Fin k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ ∧
      ∀ b ∈ B, b.Holds (FTree.toTree ∘ σ) := by sorry
