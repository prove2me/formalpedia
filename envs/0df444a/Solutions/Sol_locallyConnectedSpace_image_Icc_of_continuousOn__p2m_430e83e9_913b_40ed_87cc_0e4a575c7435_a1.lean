-- Prove2me | solution 1 for locallyConnectedSpace_image_Icc_of_continuousOn__p2m_430e83e9_913b_40ed_87cc_0e4a575c7435_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:26.160795+00:00
-- url     : https://prove2.me/submissions/81fcb5f7-49a2-4b37-878e-4f5bc11ceefe

import Mathlib

open Set

theorem solution {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (f : ℝ → X) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    LocallyConnectedSpace (f '' Set.Icc (0 : ℝ) 1) := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let t : Set X := f '' s
  letI : LocallyPathConnectedSpace s := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  letI : CompactSpace s := (isCompact_iff_compactSpace).mp isCompact_Icc
  let g : s → t := fun x => ⟨f x, Set.mem_image_of_mem f x.property⟩
  have hg : Continuous g := hf.mapsToRestrict (fun x hx => Set.mem_image_of_mem f hx)
  have hsurj : Function.Surjective g := by
    intro y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨(⟨x, hx⟩ : s), ?_⟩
    apply Subtype.ext
    exact hxy
  have hq : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj hg
  letI : LocallyPathConnectedSpace t := hq.locallyPathConnectedSpace
  change LocallyConnectedSpace t
  infer_instance