-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_le_iff_positions_le
-- name    : DeciSigma1.Semantics.Tree.le_iff_positions_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:59:30.617134+00:00
-- url     : https://prove2.me/theorems/b48f89c6-1e20-40a3-a913-19e25bf75458
-- title:
--   Tree: le iff positions le
-- statement:
--   On trees without `⊤`, the covariant order is the inclusion of constructor positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L100-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L100-L102

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

theorem DeciSigma1.Semantics.Tree.le_iff_positions_le {t u : Tree n} (ht : t.IsTopFree) (hu : u.IsTopFree) :
    t ≤ u ↔ t.positions ≤ u.positions := by sorry
