-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_realize_observations
-- name    : DeciSigma1.Full.Models.PrefixPair.realize_observations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:22:10.266833+00:00
-- url     : https://prove2.me/theorems/e24dec4b-b376-44d6-8a33-baf75f0a9a24
-- title:
--   Prefix Pair: realize observations
-- statement:
--   The Prefix Pair construction uses the realize observations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L163-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L163-L190

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
attribute [local instance] Classical.propDecidable

theorem DeciSigma1.Full.Models.PrefixPair.realize_observations (p : PrefixPair n) (w : List (Fin n)) :
    (w ∈ (nonBottomPrefixes (PrefixPair.realize p)).carrier ↔ w ∈ p.nonBottom.carrier) ∧
    (HasTopPrefix (PrefixPair.realize p) w ↔ w ∉ p.nonTop.carrier) := by sorry
