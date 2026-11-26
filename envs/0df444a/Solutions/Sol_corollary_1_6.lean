-- Prove2me | solution 1 for corollary_1_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:34:08.581976+00:00
-- url     : https://prove2.me/submissions/355c8d7d-b5b9-44ad-b9be-54d2e904fc4b

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_IsInjectiveSpace_of_retract
import Theorems.Thm_isInjectiveSpace_sierpinski_power
import Theorems.Thm_proposition_1_5

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔ ∃ (ι : Type u), Nonempty (IsRetractSubspace D (ι → Prop)) := by
  constructor
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2 (ContinuousMap.id D)
    refine ⟨Opens D, ⟨⟨productOfMemOpens D, (proposition_1_5 D).2, r, hr⟩⟩⟩
  · rintro ⟨ι, ⟨R⟩⟩
    exact IsInjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power ι) R.section' R.retraction
      R.retraction_section
