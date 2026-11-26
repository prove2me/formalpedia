-- Prove2me | solution 1 for isTightMeasureSet_couplings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:47.820555+00:00
-- url     : https://prove2.me/submissions/fa777b19-f19a-409f-a63e-d6da223916ca

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsTightMeasureSet {γm : Measure (A × B) |
      γm.map Prod.fst = (mu : Measure A) ∧ γm.map Prod.snd = (nu : Measure B)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K₁, hK₁, hK₁le⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := (mu : Measure A))) (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂, hK₂le⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := (nu : Measure B))) (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨K₁ ×ˢ K₂, hK₁.prod hK₂, ?_⟩
  rintro γm ⟨hfst, hsnd⟩
  calc γm ((K₁ ×ˢ K₂)ᶜ)
      = γm ((K₁ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ K₂ᶜ)) := by rw [Set.compl_prod_eq_union]
    _ ≤ γm (K₁ᶜ ×ˢ Set.univ) + γm (Set.univ ×ˢ K₂ᶜ) := measure_union_le _ _
    _ = (mu : Measure A) K₁ᶜ + (nu : Measure B) K₂ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
          ← Measure.map_apply measurable_fst hK₁.isClosed.measurableSet.compl,
          ← Measure.map_apply measurable_snd hK₂.isClosed.measurableSet.compl, hfst, hsnd]
    _ ≤ ε / 2 + ε / 2 :=
        add_le_add (hK₁le _ (Set.mem_singleton _)) (hK₂le _ (Set.mem_singleton _))
    _ = ε := ENNReal.add_halves ε
