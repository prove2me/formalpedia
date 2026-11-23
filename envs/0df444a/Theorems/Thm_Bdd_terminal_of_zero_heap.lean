-- Prove2me | Theorems.Thm_Bdd_terminal_of_zero_heap
-- name    : Bdd.terminal_of_zero_heap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:05:38.591045+00:00
-- url     : https://prove2.me/theorems/cc3ebe32-c27d-4262-9495-3abd9429b3c7
-- title:
--   Bdd: terminal of zero heap
-- statement:
--   The Bdd construction uses the terminal of zero heap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1819-L1824
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1819-L1824

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

theorem Bdd.terminal_of_zero_heap {B : Bdd n m} : m = 0 → ∃ b, B.root = .terminal b := by sorry
