-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_observation_bound
-- name    : DeciSigma1.Full.Models.Signed.observation_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:20:46.310419+00:00
-- url     : https://prove2.me/theorems/4c96bc48-f7f4-4450-87d3-a459d6b982e0
-- title:
--   Signed: observation bound
-- statement:
--   An observation of a signed configuration holds exactly when its ground bound holds in the
--   order with variance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L315-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L315-L320

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Full_Models_observation_bound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Full.Closure DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}

theorem DeciSigma1.Full.Models.Signed.observation_bound {V : Type*} (c : Fin n → Bool)
    (ρ : V → Semantics.Tree n) (o : Observation n V) :
    (o.bound c).HoldsWithVariance c ρ ↔ o.Holds c ρ := by sorry
