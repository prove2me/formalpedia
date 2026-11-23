-- Prove2me | Theorems.Thm_Bdd_eq_terminal_of_relevant
-- name    : Bdd.eq_terminal_of_relevant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:10.328332+00:00
-- url     : https://prove2.me/theorems/bf309769-3857-45f4-bb12-6155e342f2d5
-- title:
--   Bdd: eq terminal of relevant
-- statement:
--   The Bdd construction uses the eq terminal of relevant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L569-L571
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L569-L571

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

theorem Bdd.eq_terminal_of_relevant {n m} {v : Vector (Node n m) m} {B : Bdd n m} (h : B = {heap := v, root := terminal b}) (S : B.RelevantPointer) :
    S.1 = terminal b := by sorry
