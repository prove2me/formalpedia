-- Prove2me | solution 1 for not_isTerminal_of_root_eq_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:03:13.088373+00:00
-- url     : https://prove2.me/submissions/f09f3e80-c3c8-46df-9984-b2d028ca410b

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
theorem _root_.solution {n m} {j} {O : OBdd n m} (h : O.1.root = node j) : ¬ O.isTerminal := by
  rintro ⟨b, hb⟩
  rw [h] at hb
  contradiction
