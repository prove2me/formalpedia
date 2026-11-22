-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_observation_normalized
-- name    : DeciSigma1.Full.Models.Signed.observation_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:20:24.796797+00:00
-- url     : https://prove2.me/theorems/5b6787bb-9a45-4f97-b306-b9c28eb00a63
-- title:
--   Signed: observation normalized
-- statement:
--   The Signed construction uses the observation normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L292-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L292-L305

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
open DeciSigma1.Full.Closure DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}

theorem DeciSigma1.Full.Models.Signed.observation_normalized {V : Type*} (c : Fin n → Bool)
    (ρ : V → Semantics.Tree n) (o : Observation n V) :
    o.normalized.Holds (fun v => Tree.normalize c false (ρ v)) ↔ o.Holds c ρ := by sorry
