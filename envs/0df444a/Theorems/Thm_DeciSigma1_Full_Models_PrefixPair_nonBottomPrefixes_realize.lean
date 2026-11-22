-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_nonBottomPrefixes_realize
-- name    : DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:19:16.844795+00:00
-- url     : https://prove2.me/theorems/1ae747c4-258c-4991-86e6-24d417427d10
-- title:
--   Prefix Pair: non Bottom Prefixes realize
-- statement:
--   The Prefix Pair construction uses the non Bottom Prefixes realize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L192-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L192-L194

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

theorem DeciSigma1.Full.Models.PrefixPair.nonBottomPrefixes_realize (p : PrefixPair n) :
    nonBottomPrefixes (PrefixPair.realize p) = p.nonBottom := by sorry
