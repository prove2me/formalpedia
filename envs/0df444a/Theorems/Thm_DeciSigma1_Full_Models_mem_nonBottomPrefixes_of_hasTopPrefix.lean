-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_mem_nonBottomPrefixes_of_hasTopPrefix
-- name    : DeciSigma1.Full.Models.mem_nonBottomPrefixes_of_hasTopPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:04.155854+00:00
-- url     : https://prove2.me/theorems/fa51d91e-e3b2-486c-b9d0-0166fdde6c25
-- title:
--   Models: mem non Bottom Prefixes of has Top Prefix
-- statement:
--   The Models construction uses the mem non Bottom Prefixes of has Top Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L78-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L78-L83

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

theorem DeciSigma1.Full.Models.mem_nonBottomPrefixes_of_hasTopPrefix (t : Semantics.Tree n) (w : List (Fin n)) :
    HasTopPrefix t w → w ∈ (nonBottomPrefixes t).carrier := by sorry
