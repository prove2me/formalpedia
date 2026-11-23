-- Prove2me | Theorems.Thm_DecisionTree_relabel_injective
-- name    : DecisionTree.relabel_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:41.469952+00:00
-- url     : https://prove2.me/theorems/6a2098d9-b9f7-4832-90ed-33ba38c44ae3
-- title:
--   Decision Tree: relabel injective
-- statement:
--   The Decision Tree construction uses the relabel injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L81-L105
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L81-L105

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree
set_option autoImplicit true
open DecisionTree

theorem DecisionTree.relabel_injective {f : Nat → Nat} {hf : ∀ i : Fin n, f i < f n} {h : ∀ i i' : Fin n, T1.usesVar i → T2.usesVar i' → f i = f i' → i = i'} :
    relabel hf T1 = relabel hf T2 → T1 = T2 := by sorry
