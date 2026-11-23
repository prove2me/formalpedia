-- Prove2me | Theorems.Thm_Bdd_low_root_eq_low
-- name    : Bdd.low_root_eq_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:54.840042+00:00
-- url     : https://prove2.me/theorems/8d426eda-217f-4217-b505-0d540ca483f8
-- title:
--   Bdd: low root eq low
-- statement:
--   The Bdd construction uses the low root eq low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L288-L288
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L288-L288

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

theorem Bdd.low_root_eq_low {B : Bdd n m} {h : B.root = node j} : (B.low h).root = B.heap[j].low := by sorry
