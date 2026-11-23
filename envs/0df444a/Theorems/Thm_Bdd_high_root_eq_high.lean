-- Prove2me | Theorems.Thm_Bdd_high_root_eq_high
-- name    : Bdd.high_root_eq_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:57:57.32795+00:00
-- url     : https://prove2.me/theorems/9ec994aa-6086-4d62-a55f-47228b15837f
-- title:
--   Bdd: high root eq high
-- statement:
--   The Bdd construction uses the high root eq high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L291-L291
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L291-L291

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

theorem Bdd.high_root_eq_high {B : Bdd n m} {h : B.root = node j} : (B.high h).root = B.heap[j].high := by sorry
