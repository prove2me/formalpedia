-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_node_bot_le_iff
-- name    : DeciSigma1.Full.Models.node_bot_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:32.712981+00:00
-- url     : https://prove2.me/theorems/f31fa286-c1d2-4bf3-b5d5-5a95bec8b474
-- title:
--   Models: node bot le iff
-- statement:
--   The Models construction uses the node bot le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L264-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L264-L267

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

theorem DeciSigma1.Full.Models.node_bot_le_iff (t : Semantics.Tree n) :
    Semantics.Tree.node (fun _ => Tree.bot) ≤ t ↔ t ≠ Tree.bot := by sorry
