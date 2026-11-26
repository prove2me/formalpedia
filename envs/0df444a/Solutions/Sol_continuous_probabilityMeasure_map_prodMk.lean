-- Prove2me | solution 1 for continuous_probabilityMeasure_map_prodMk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:46.809231+00:00
-- url     : https://prove2.me/submissions/523fa41e-84c8-4026-970a-f6ab79507975

import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {H W : Type*}
  [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]
theorem _root_.solution :
    Continuous (fun p : H × ProbabilityMeasure W =>
      ProbabilityMeasure.map p.2
        (measurable_prodMk_left (x := p.1)).aemeasurable) := by
  refine SeqContinuous.continuous fun ps p hps => ?_
  have hx : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hps
  have hγ : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hps
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf' fun G hG => ?_
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply measurable_prodMk_left hG.measurableSet]
  refine le_of_forall_lt fun r hr => ?_
  -- inner regularity: a compact K inside the section of G over p.1
  obtain ⟨K, hKsub, hKc, hK⟩ :=
    (hG.measurableSet.preimage measurable_prodMk_left).exists_lt_isCompact_of_ne_top
      (measure_ne_top _ _) hr
  -- tube lemma around {p.1} ×ˢ K
  have hxK : {p.1} ×ˢ K ⊆ G := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact hKsub hz
  obtain ⟨V, O, hVopen, hOopen, hxV, hKO, hVO⟩ :=
    generalized_tube_lemma isCompact_singleton hKc hG hxK
  -- eventually the moving section contains O
  have hev : ∀ᶠ n in atTop,
      ((ps n).2 : Measure W) O
        ≤ (((ps n).2 : Measure W).map (Prod.mk (ps n).1)) G := by
    filter_upwards [hx.eventually
      (hVopen.mem_nhds (Set.singleton_subset_iff.mp hxV))] with n hn
    rw [Measure.map_apply measurable_prodMk_left hG.measurableSet]
    exact measure_mono fun z hz => hVO ⟨hn, hz⟩
  calc r < (p.2 : Measure W) K := hK
    _ ≤ (p.2 : Measure W) O := measure_mono hKO
    _ ≤ atTop.liminf (fun n => ((ps n).2 : Measure W) O) :=
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hγ hOopen
    _ ≤ atTop.liminf
          (fun n => (((ps n).2 : Measure W).map (Prod.mk (ps n).1)) G) :=
        liminf_le_liminf hev
