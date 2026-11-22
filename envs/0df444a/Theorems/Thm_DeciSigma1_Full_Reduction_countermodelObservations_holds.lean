-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_countermodelObservations_holds
-- name    : DeciSigma1.Full.Reduction.countermodelObservations_holds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:29.368869+00:00
-- url     : https://prove2.me/theorems/2b3308db-1a10-44b0-8fb4-0eb5446dfbc1
-- title:
--   Reduction: countermodel Observations holds
-- statement:
--   The Reduction construction uses the countermodel Observations holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L55-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L55-L61

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}

theorem DeciSigma1.Full.Reduction.countermodelObservations_holds (ρ : V → Semantics.Tree n) (m : Fin k → Bool)
    (W : Fin k → List (Fin n)) :
    (∀ o ∈ countermodelObservations q m W, o.Holds c ρ) ↔
      ∀ i, seed (q i) (m i) (W i) ∈ Closure.configSet c ρ ∧
        exclusion (q i) (m i) (W i) ∉ Closure.configSet c ρ := by sorry
