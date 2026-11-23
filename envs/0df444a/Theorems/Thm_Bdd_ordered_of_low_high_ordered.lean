-- Prove2me | Theorems.Thm_Bdd_ordered_of_low_high_ordered
-- name    : Bdd.ordered_of_low_high_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:25.872915+00:00
-- url     : https://prove2.me/theorems/e05970c4-5dba-42a1-b72d-b0ba5689b950
-- title:
--   Bdd: ordered of low high ordered
-- statement:
--   The Bdd construction uses the ordered of low high ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1219-L1251
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1219-L1251

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

theorem Bdd.ordered_of_low_high_ordered {B : Bdd n m} (h : B.root = node j):
    (B.low h).Ordered → B.var < (B.low h).var → (B.high h).Ordered → B.var < (B.high h).var → Ordered B := by sorry
