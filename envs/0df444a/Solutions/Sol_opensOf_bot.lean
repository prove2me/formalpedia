-- Prove2me | solution 1 for opensOf_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:14.75377+00:00
-- url     : https://prove2.me/submissions/ed466a3f-5416-4731-b2da-c44bac59bd63

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_isOpen_bot

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem _root_.solution : opensOf (⊥ : TopologicalSpace α) = univ := by
  ext U
  exact ⟨fun _ => mem_univ U, fun _ => isOpen_bot U⟩
