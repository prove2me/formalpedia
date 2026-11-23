-- Prove2me | Theorems.Thm_Bdd_ordered_of_ordered_heap_not_reachable_set
-- name    : Bdd.ordered_of_ordered_heap_not_reachable_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:05:23.988504+00:00
-- url     : https://prove2.me/theorems/de06794c-639d-428b-9b07-34f1b09b04b2
-- title:
--   Bdd: ordered of ordered heap not reachable set
-- statement:
--   The Bdd construction uses the ordered of ordered heap not reachable set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1253-L1347
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1253-L1347

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

theorem Bdd.ordered_of_ordered_heap_not_reachable_set (O : OBdd n m) :
    ∀ i N, ¬ Reachable O.1.heap O.1.root (node i) → Ordered ⟨O.1.heap.set i N, O.1.root⟩ := by sorry
