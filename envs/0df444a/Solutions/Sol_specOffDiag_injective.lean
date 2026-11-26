-- Prove2me | solution 1 for specOffDiag_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:18.694237+00:00
-- url     : https://prove2.me/submissions/c00837dc-9acf-4c29-beeb-91d1b2cdf56a

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_specSet_injective

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution :
    Function.Injective (specOffDiag : TopologicalSpace α → Set {p : α × α // p.1 ≠ p.2}) := by
  intro t₁ t₂ h
  refine specSet_injective ?_
  ext p
  obtain ⟨x, y⟩ := p
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_true (@specializes_rfl α t₁ x) (@specializes_rfl α t₂ x)
  · simpa [specSet, specOffDiag] using (Set.ext_iff.mp h ⟨(x, y), hxy⟩)
