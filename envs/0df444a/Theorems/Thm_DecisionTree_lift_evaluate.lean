-- Prove2me | Theorems.Thm_DecisionTree_lift_evaluate
-- name    : DecisionTree.lift_evaluate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:39.686412+00:00
-- url     : https://prove2.me/theorems/02664062-6b9e-41f9-b57a-c1c661c08dc2
-- title:
--   Decision Tree: lift evaluate
-- statement:
--   The Decision Tree construction uses the lift evaluate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L61-L75
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/DecisionTree.lean#L61-L75

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree
set_option autoImplicit true
open DecisionTree

theorem DecisionTree.lift_evaluate {h : n ≤ n'} {T : DecisionTree n} {I : Vector Bool n'} :
    (lift h T).evaluate I = T.evaluate (Vector.cast (show (min n n') = n by simpa) (I.take n)) := by sorry
