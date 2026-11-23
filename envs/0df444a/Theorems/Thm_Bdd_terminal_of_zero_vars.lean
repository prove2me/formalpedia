-- Prove2me | Theorems.Thm_Bdd_terminal_of_zero_vars
-- name    : Bdd.terminal_of_zero_vars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:05:34.097381+00:00
-- url     : https://prove2.me/theorems/d5380342-9473-41c7-b9b6-c683eda95aa9
-- title:
--   Bdd: terminal of zero vars
-- statement:
--   The Bdd construction uses the terminal of zero vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1812-L1817
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1812-L1817

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

theorem Bdd.terminal_of_zero_vars {B : Bdd n m} : n = 0 → ∃ b, B.root = .terminal b := by sorry
