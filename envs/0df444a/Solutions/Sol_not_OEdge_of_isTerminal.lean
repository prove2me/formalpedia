-- Prove2me | solution 1 for not_OEdge_of_isTerminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:38.265165+00:00
-- url     : https://prove2.me/submissions/6559c8b9-5e1a-446a-8e00-67ee1a55026b

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
theorem _root_.solution {O : OBdd n m}: O.isTerminal → ¬ OEdge O U := by
  rintro ⟨b, h⟩ ⟨_, contra⟩
  rw [h] at contra
  exact not_terminal_edge contra
