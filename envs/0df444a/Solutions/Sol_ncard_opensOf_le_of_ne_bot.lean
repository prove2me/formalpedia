-- Prove2me | solution 1 for ncard_opensOf_le_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:50.723891+00:00
-- url     : https://prove2.me/submissions/baf4c684-d560-43a7-ac01-b237f74df1ba

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_exists_specializes_of_ne_bot
import Theorems.Thm_ncard_opens_of_specialization

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    ncard (opensOf t) ≤ 3 * 2 ^ (Fintype.card α - 2) := by
  obtain ⟨x, y, hne, hy⟩ := exists_specializes_of_ne_bot ht
  exact ncard_opens_of_specialization hne hy
