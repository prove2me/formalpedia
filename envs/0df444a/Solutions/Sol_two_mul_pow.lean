-- Prove2me | solution 1 for two_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:55.200491+00:00
-- url     : https://prove2.me/submissions/69f61759-e6fd-44b2-a2b3-1ccf29b318f9

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
variable {x y : α}
theorem _root_.solution (a : ℕ) : 2 ^ a * 2 = 2 * 2 ^ a := by
  rw [mul_comm]
