-- Prove2me | Theorems.Thm_Evaluate_evaluate_node
-- name    : Evaluate.evaluate_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:05.966811+00:00
-- url     : https://prove2.me/theorems/fe7054bc-6223-4678-a6ce-369930d62ae0
-- title:
--   Evaluate: evaluate node
-- statement:
--   The Evaluate construction uses the evaluate node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Evaluate.lean#L28-L32
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Evaluate.lean#L28-L32

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Evaluate
set_option autoImplicit true
open Evaluate

theorem Evaluate.evaluate_node {O : OBdd n m} (h : O.1.root = .node j) :
    evaluate O = fun I ↦ if I[O.1.heap[j].var] then evaluate (O.high h) I else evaluate (O.low h) I := by sorry
