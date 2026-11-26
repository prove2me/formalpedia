-- Prove2me | solution 1 for isTightMeasureSet_range_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:20.075285+00:00
-- url     : https://prove2.me/submissions/08e18f6c-cd18-4888-b3be-2f7bcb654886

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC

set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
theorem _root_.solution {Ω : Type*}
    [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {γs : ℕ → ProbabilityMeasure Ω} {γ : ProbabilityMeasure Ω}
    (hγ : Tendsto γs atTop (𝓝 γ)) :
    IsTightMeasureSet {((γs n : ProbabilityMeasure Ω) : Measure Ω) | n : ℕ} := by
  have hins : IsCompact (insert γ (Set.range γs)) := hγ.isCompact_insert_range
  have hclos : IsCompact (closure (Set.range γs)) :=
    hins.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert γ (Set.range γs)) hins.isClosed)
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable Ω
  have htight := isTightMeasureSet_of_isCompact_closure hclos
  have hset : {((μ : ProbabilityMeasure Ω) : Measure Ω) | μ ∈ Set.range γs}
      = {((γs n : ProbabilityMeasure Ω) : Measure Ω) | n : ℕ} := by
    ext m
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨γs n, ⟨n, rfl⟩, rfl⟩
  rwa [hset] at htight
