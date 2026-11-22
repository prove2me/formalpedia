-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_le_dual_iff
-- name    : DeciSigma1.Full.Models.le_dual_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:43.311337+00:00
-- url     : https://prove2.me/theorems/261a8b9a-d06f-487b-a786-9f125fbc6902
-- title:
--   Models: le dual iff
-- statement:
--   The Models construction uses the le dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L282-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L282-L284

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

theorem DeciSigma1.Full.Models.le_dual_iff (t : Semantics.Tree n) (g : FTree n) :
    t ≤ g.dual.toTree ↔ g.toTree ≤ Tree.dual t := by sorry
