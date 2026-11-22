-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_IsTopFree_subtrees_finite_iff
-- name    : DeciSigma1.Semantics.Tree.IsTopFree.subtrees_finite_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:56.933516+00:00
-- url     : https://prove2.me/theorems/170fe0b1-292c-49c3-9c9a-3f074f805ffb
-- title:
--   Is Top Free: subtrees finite iff
-- statement:
--   A tree without `⊤` has finitely many subtrees exactly when its set of constructor positions
--   has finitely many residuals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L205-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Embedding.lean#L205-L221

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

theorem DeciSigma1.Semantics.Tree.IsTopFree.subtrees_finite_iff {t : Tree n} (ht : t.IsTopFree) :
    (Characterization.subtrees t).Finite ↔ IsRegularTree t.positions := by sorry
