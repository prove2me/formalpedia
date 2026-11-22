-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_positions_le_of_le
-- name    : DeciSigma1.Semantics.Tree.positions_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:43.92174+00:00
-- url     : https://prove2.me/theorems/45315046-faf3-43c7-9bf0-d4f1bf864baa
-- title:
--   Tree: positions le of le
-- statement:
--   If `⊤` does not occur in `u`, the covariant order `t ≤ u` gives the inclusion of
--   constructor positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L75-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L75-L87

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Mathlib.Data.Set.Finite.List
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree

theorem DeciSigma1.Semantics.Tree.positions_le_of_le {t u : Tree n} (hu : u.IsTopFree) (h : t ≤ u) :
    t.positions ≤ u.positions := by sorry
