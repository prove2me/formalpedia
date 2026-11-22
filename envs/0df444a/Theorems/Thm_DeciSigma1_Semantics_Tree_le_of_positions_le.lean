-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_le_of_positions_le
-- name    : DeciSigma1.Semantics.Tree.le_of_positions_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:35.019866+00:00
-- url     : https://prove2.me/theorems/b877565c-3abd-4a64-b188-d13333a8b3a0
-- title:
--   Tree: le of positions le
-- statement:
--   If `⊤` does not occur in `t`, the inclusion of constructor positions gives the covariant
--   order `t ≤ u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L91-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L91-L97

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

theorem DeciSigma1.Semantics.Tree.le_of_positions_le {t u : Tree n} (ht : t.IsTopFree) (h : t.positions ≤ u.positions) :
    t ≤ u := by sorry
