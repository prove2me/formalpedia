-- Prove2me | Theorems.Thm_Bdd_reduced_of_terminal
-- name    : Bdd.reduced_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:55:55.175795+00:00
-- url     : https://prove2.me/theorems/4b6444dd-d9a8-4fea-8093-f6f5340fbea9
-- title:
--   Bdd: reduced of terminal
-- statement:
--   The Bdd construction uses the reduced of terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L585-L585
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L585-L585

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

theorem Bdd.reduced_of_terminal : OBdd.Reduced ⟨⟨M, terminal b⟩, o⟩ := by sorry
