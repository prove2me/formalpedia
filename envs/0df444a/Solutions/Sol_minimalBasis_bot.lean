-- Prove2me | solution 1 for minimalBasis_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:00.729845+00:00
-- url     : https://prove2.me/submissions/b82a128b-61d8-48a0-ac63-08d55a0399ee

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_minimalOpen_bot

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem _root_.solution :
    minimalBasis (⊥ : TopologicalSpace α) = range (singleton : α → Set α) := by
  ext U
  simp [minimalBasis, minimalOpen_bot, singleton]
