-- Prove2me | solution 1 for specSet_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:36.450404+00:00
-- url     : https://prove2.me/submissions/6367f0b4-a70e-4c7e-949a-c9ca00ed5901

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
omit [DecidableEq α]
theorem _root_.solution :
    Function.Injective (specSet : TopologicalSpace α → Set (α × α)) := by
  intro t₁ t₂ h
  have hmin : ∀ z, minimalOpen t₁ z = minimalOpen t₂ z := by
    intro z
    ext w
    have : @Specializes α t₁ w z ↔ @Specializes α t₂ w z := by
      simpa [specSet] using (Set.ext_iff.mp h (w, z))
    simpa [minimalOpen, mem_nhdsKer_singleton] using this
  have : minimalBasis t₁ = minimalBasis t₂ := by
    ext U
    simp [minimalBasis, hmin]
  exact (generateFrom_minimalBasis t₁).symm.trans
    ((congrArg generateFrom this).trans (generateFrom_minimalBasis t₂))
