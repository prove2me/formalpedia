-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_realize_node
-- name    : DeciSigma1.Full.Models.PrefixPair.realize_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:29.777571+00:00
-- url     : https://prove2.me/theorems/1ada1be5-3633-447b-8d4f-9f6b9bba0c84
-- title:
--   Prefix Pair: realize node
-- statement:
--   The Prefix Pair construction uses the realize node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L153-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L153-L161

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

theorem DeciSigma1.Full.Models.PrefixPair.realize_node (p : PrefixPair n) (hc : [] ∈ p.nonBottom.carrier)
    (hn : [] ∈ p.nonTop.carrier) :
    PrefixPair.realize p = Semantics.Tree.node (fun i => PrefixPair.realize (p.child i)) := by sorry
