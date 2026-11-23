-- Prove2me | Theorems.Thm_DecisionTree_usesVar_iff
-- name    : DecisionTree.usesVar_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:35.271365+00:00
-- url     : https://prove2.me/theorems/a15f7b3b-c5f9-4c45-ba19-4abbe0a3cd8f
-- title:
--   Decision Tree: uses Var iff
-- statement:
--   The Decision Tree construction uses the uses Var iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L23-L37
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L23-L37

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree
set_option autoImplicit true
open DecisionTree

theorem DecisionTree.usesVar_iff (i : Fin n) (T : DecisionTree n) :
    T.usesVar i ↔ (∃ i' l h, T = .branch i' l h ∧ (i = i' ∨ l.usesVar i ∨ h.usesVar i)) := by sorry
