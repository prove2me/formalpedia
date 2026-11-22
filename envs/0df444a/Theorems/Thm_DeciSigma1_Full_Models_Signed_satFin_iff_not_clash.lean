-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_satFin_iff_not_clash
-- name    : DeciSigma1.Full.Models.Signed.satFin_iff_not_clash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:24:11.244813+00:00
-- url     : https://prove2.me/theorems/c59f7dc6-0f9e-42ca-9a9d-2021d2eeef99
-- title:
--   Signed: sat Fin iff not clash
-- statement:
--   A constraint with variance has a finite solution exactly when its signed translation has
--   neither a label clash nor a cycle clash.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L340-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L340-L343

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

theorem DeciSigma1.Full.Models.Signed.satFin_iff_not_clash {V : Type*} [Finite V]
    (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SatFin c Γ ↔ ¬ LabelClash (signed c Γ) ∧ ¬ CycleClash (signed c Γ) := by sorry
