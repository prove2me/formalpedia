-- Prove2me | Theorems.Thm_Bdd_terminal_relevant_iff
-- name    : Bdd.terminal_relevant_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:05.137704+00:00
-- url     : https://prove2.me/theorems/45536751-00d7-4651-8a92-b5458bc3e04e
-- title:
--   Bdd: terminal relevant iff
-- statement:
--   The graph induced by a terminal BDD consists of a sole terminal pointer.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L561-L567
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L561-L567

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

theorem Bdd.terminal_relevant_iff {n m} {B : Bdd n m} (h : B.root = terminal b) (S : B.RelevantPointer) {motive : Pointer m → Prop} :
    motive S.1 ↔ motive (terminal b) := by sorry
