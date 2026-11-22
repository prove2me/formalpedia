-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_observation_bound
-- name    : DeciSigma1.Full.Models.observation_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:29.680826+00:00
-- url     : https://prove2.me/theorems/b73cd413-e3ef-40cd-94ec-1be69aca257e
-- title:
--   Models: observation bound
-- statement:
--   An observation holds exactly when its ground bound holds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L303-L317
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L303-L317

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models
open DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Models.observation_bound {V : Type*} (ρ : V → Semantics.Tree n) (o : Observation n V) :
    o.bound.Holds ρ ↔ o.Holds ρ := by sorry
