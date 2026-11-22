-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_mem_nonBottomPrefixes_dual
-- name    : DeciSigma1.Full.Models.mem_nonBottomPrefixes_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:19.050341+00:00
-- url     : https://prove2.me/theorems/3d9218f6-cb97-4b34-ab74-8d7226afccf3
-- title:
--   Models: mem non Bottom Prefixes dual
-- statement:
--   The Models construction uses the mem non Bottom Prefixes dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L95-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L95-L96

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

theorem DeciSigma1.Full.Models.mem_nonBottomPrefixes_dual (t : Semantics.Tree n) (w : List (Fin n)) :
    w ∈ (nonBottomPrefixes (Tree.dual t)).carrier ↔ ¬ HasTopPrefix t w := by sorry
