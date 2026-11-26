-- Prove2me | solution 1 for ncard_opens_of_specialization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:26.153142+00:00
-- url     : https://prove2.me/submissions/a7d2fa6c-1d6c-4cb8-96a4-ab6c065cc38e

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_constrained

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution {t : TopologicalSpace α}
    (hne : x ≠ y) (hy : y ∈ minimalOpen t x) :
    ncard (opensOf t) ≤ 3 * 2 ^ (Fintype.card α - 2) := by
  have hsub : opensOf t ⊆ {U : Set α | x ∈ U → y ∈ U} := by
    intro U hU hxU
    exact minimalOpen_subset_of_isOpen t hU hxU hy
  exact (ncard_le_ncard hsub).trans (card_constrained hne)
