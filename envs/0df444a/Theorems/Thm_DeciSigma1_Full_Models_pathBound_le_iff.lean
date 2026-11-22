-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_pathBound_le_iff
-- name    : DeciSigma1.Full.Models.pathBound_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:24:32.481803+00:00
-- url     : https://prove2.me/theorems/446e09f7-5517-43f7-af8c-bab05dbc3e54
-- title:
--   Models: path Bound le iff
-- statement:
--   The Models construction uses the path Bound le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L246-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Observations.lean#L246-L262

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

theorem DeciSigma1.Full.Models.pathBound_le_iff (w : List (Fin n)) (g : FTree n) (hg : g.toTree ≠ Tree.bot)
    (t : Semantics.Tree n) :
    (pathBound w g).toTree ≤ t ↔ g.toTree ≤ Semantics.Tree.trace t w := by sorry
