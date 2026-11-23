-- Prove2me | Theorems.Thm_DecisionTree_lift_injective
-- name    : DecisionTree.lift_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:42.917387+00:00
-- url     : https://prove2.me/theorems/f3269504-4860-4ee2-9463-8ea72fd09884
-- title:
--   Decision Tree: lift injective
-- statement:
--   The Decision Tree construction uses the lift injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L43-L59
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L43-L59

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree
set_option autoImplicit true
open DecisionTree

theorem DecisionTree.lift_injective {n n' : Nat} {h : n ≤ n'} : Function.Injective (lift h) := by sorry
