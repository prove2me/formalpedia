-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_satFin_iff_finite_assignment
-- name    : DeciSigma1.Full.Models.satFin_iff_finite_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:24:39.83091+00:00
-- url     : https://prove2.me/theorems/899dedae-417a-484b-822e-38d648f9e7e0
-- title:
--   Models: sat Fin iff finite assignment
-- statement:
--   Finite satisfiability can be witnessed by an assignment of finite trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L341-L348
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L341-L348

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Models.satFin_iff_finite_assignment {V : Type*} (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SatFin c Γ ↔ ∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) Γ := by sorry
