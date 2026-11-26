-- Prove2me | solution 1 for minimalBasis_subset_opens
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:44:25.328197+00:00
-- url     : https://prove2.me/submissions/1b5fe6ef-2f6a-435f-bd0c-848bdb55dd52

import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Sum
import Definitions.Def_CARDB

set_option autoImplicit true
open Set TopologicalSpace
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (t : TopologicalSpace α)
omit [DecidableEq α]
theorem _root_.solution : minimalBasis t ⊆ opensOf t := by
  rintro _ ⟨x, rfl⟩
  exact isOpen_minimalOpen t x
