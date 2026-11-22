-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_boundRealization_finiteTop
-- name    : DeciSigma1.Full.Models.Signed.boundRealization_finiteTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:05.667802+00:00
-- url     : https://prove2.me/theorems/dac5defb-f79e-4321-8e26-b077e914c1b5
-- title:
--   Signed: bound Realization finite Top
-- statement:
--   For a constraint with a finite solution, finitely many ground bounds that hold together in
--   some solution hold together in a finite solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L354-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L354-L356

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Satisfiability DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}

theorem DeciSigma1.Full.Models.Signed.boundRealization_finiteTop {V : Type*} (c : Fin n → Bool)
    (Γ : List (LitT n V)) (hf : SatFin c Γ) : BoundRealization FiniteTop c Γ := by sorry
