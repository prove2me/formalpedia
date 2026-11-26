-- Prove2me | solution 1 for minimalOpen_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:18.347781+00:00
-- url     : https://prove2.me/submissions/677f9c77-c817-47ca-b7c4-c5880ba31369

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
theorem _root_.solution (x : α) :
    minimalOpen (⊥ : TopologicalSpace α) x = {x} :=
  @IsOpen.nhdsKer_eq α ⊥ {x} (isOpen_bot {x})
