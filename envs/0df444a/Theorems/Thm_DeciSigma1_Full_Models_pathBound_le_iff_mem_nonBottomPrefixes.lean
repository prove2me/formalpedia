-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_pathBound_le_iff_mem_nonBottomPrefixes
-- name    : DeciSigma1.Full.Models.pathBound_le_iff_mem_nonBottomPrefixes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:37.8072+00:00
-- url     : https://prove2.me/theorems/6a75b328-dd61-4bb3-aadb-15c5c1fbfd22
-- title:
--   Models: path Bound le iff mem non Bottom Prefixes
-- statement:
--   The Models construction uses the path Bound le iff mem non Bottom Prefixes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L269-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L269-L274

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

theorem DeciSigma1.Full.Models.pathBound_le_iff_mem_nonBottomPrefixes (t : Semantics.Tree n) (w : List (Fin n)) :
    (pathBound w (.node (fun _ => .bot))).toTree ≤ t ↔ w ∈ (nonBottomPrefixes t).carrier := by sorry
