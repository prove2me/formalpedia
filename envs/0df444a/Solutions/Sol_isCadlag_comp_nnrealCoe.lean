-- Prove2me | solution 1 for isCadlag_comp_nnrealCoe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:08:09.911866+00:00
-- url     : https://prove2.me/submissions/300717bd-4fb6-40a2-85f2-17c6590dcfc3

import Definitions.Def_LeanLevy_Processes_Cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology ProbabilityTheory
open scoped NNReal
universe u₃
variable {β : Type u₃} [TopologicalSpace β]

theorem solution {f : ℝ → β} (hf : IsCadlag f) :
    IsCadlag (fun t : ℝ≥0 => f t) := by
  intro t
  constructor
  · have hmap : Set.MapsTo ((↑) : ℝ≥0 → ℝ) (Ici t) (Ici (t : ℝ)) :=
      fun s hs => NNReal.coe_le_coe.mpr hs
    exact (hf (t : ℝ)).1.comp NNReal.continuous_coe.continuousWithinAt hmap
  · obtain ⟨l, hl⟩ := (hf (t : ℝ)).2
    refine ⟨l, ?_⟩
    have hmap : Set.MapsTo ((↑) : ℝ≥0 → ℝ) (Iio t) (Iio (t : ℝ)) :=
      fun s hs => NNReal.coe_lt_coe.mpr hs
    have htend : Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝[Iio t] t) (𝓝[Iio (t : ℝ)] (t : ℝ)) :=
      NNReal.continuous_coe.continuousWithinAt.tendsto_nhdsWithin hmap
    exact hl.comp htend