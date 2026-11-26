-- Prove2me | solution 1 for singleton_set_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:22.99591+00:00
-- url     : https://prove2.me/submissions/d5bbad31-ffd0-4f65-a671-555b5d6b9d79

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
theorem _root_.solution : Function.Injective (singleton : α → Set α) :=
  fun x y h => by
    have : x ∈ ({y} : Set α) := (Set.ext_iff.mp h x).1 (mem_singleton x)
    simpa using this
