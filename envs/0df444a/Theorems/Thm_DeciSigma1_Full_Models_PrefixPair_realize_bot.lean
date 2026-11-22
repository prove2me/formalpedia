-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_realize_bot
-- name    : DeciSigma1.Full.Models.PrefixPair.realize_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:27.287791+00:00
-- url     : https://prove2.me/theorems/f0aaf432-f1f7-4247-8b9d-263d5214ac9a
-- title:
--   Prefix Pair: realize bot
-- statement:
--   The Prefix Pair construction uses the realize bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L140-L144
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L140-L144

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

theorem DeciSigma1.Full.Models.PrefixPair.realize_bot (p : PrefixPair n) (h : [] ∉ p.nonBottom.carrier) :
    PrefixPair.realize p = Tree.bot := by sorry
