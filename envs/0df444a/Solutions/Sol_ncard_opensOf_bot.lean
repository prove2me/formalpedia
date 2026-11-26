-- Prove2me | solution 1 for ncard_opensOf_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:53.46722+00:00
-- url     : https://prove2.me/submissions/00047091-395d-412b-8478-9b766e13f8f2

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_opensOf_bot

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem _root_.solution :
    ncard (opensOf (⊥ : TopologicalSpace α)) = 2 ^ Fintype.card α := by
  rw [opensOf_bot, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_set]
