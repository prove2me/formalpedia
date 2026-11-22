-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_positions_subtree
-- name    : DeciSigma1.Semantics.Tree.positions_subtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:43.246197+00:00
-- url     : https://prove2.me/theorems/6088627d-6975-4ae4-8eed-cde60c638b5c
-- title:
--   Tree: positions subtree
-- statement:
--   The constructor positions of the subtree at `π` are the residual at `π`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L128-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L128-L130

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

theorem DeciSigma1.Semantics.Tree.positions_subtree {t u : Tree n} {π : List (Fin n)} (h : t.subtree π = some u) :
    u.positions = t.positions.residual π := by sorry
