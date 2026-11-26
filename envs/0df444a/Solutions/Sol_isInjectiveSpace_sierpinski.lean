-- Prove2me | solution 1 for isInjectiveSpace_sierpinski
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:31:33.105856+00:00
-- url     : https://prove2.me/submissions/a0d90cd4-6554-474f-a91e-a6ad70335000

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution : IsInjectiveSpace.{u} Prop := by
  intro X Y _ _ e he f
  have hfopen : IsOpen {x | f x} := continuous_Prop.1 f.continuous
  rw [he.isInducing.isOpen_iff] at hfopen
  obtain ⟨V, hVopen, hVeq⟩ := hfopen
  refine ⟨⟨fun y => y ∈ V, continuous_Prop.2 hVopen⟩, fun x => ?_⟩
  have : (e x ∈ V) = (x ∈ {x | f x}) := by rw [← hVeq]; rfl
  simpa using this
