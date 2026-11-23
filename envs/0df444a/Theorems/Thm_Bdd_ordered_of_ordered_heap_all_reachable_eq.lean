-- Prove2me | Theorems.Thm_Bdd_ordered_of_ordered_heap_all_reachable_eq
-- name    : Bdd.ordered_of_ordered_heap_all_reachable_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:45.602644+00:00
-- url     : https://prove2.me/theorems/1ef3ddef-a5b9-4e02-87f0-5695b6eecc5a
-- title:
--   Bdd: ordered of ordered heap all reachable eq
-- statement:
--   The Bdd construction uses the ordered of ordered heap all reachable eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1905-L1994
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1905-L1994

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered

theorem Bdd.ordered_of_ordered_heap_all_reachable_eq (O : OBdd n m) (B : Bdd n m') :
    (∀ j : Fin m', Reachable B.heap B.root (node j) → ∃ hj : j.1 < m, Node.equiv O.1.heap[j.1] B.heap[j]) →
    (∀ j, B.root = .node j → ∃ hj, O.1.root = .node ⟨j.1, hj⟩) →
    Ordered B := by sorry
