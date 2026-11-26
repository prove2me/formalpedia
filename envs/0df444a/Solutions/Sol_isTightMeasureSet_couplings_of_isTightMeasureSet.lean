-- Prove2me | solution 1 for isTightMeasureSet_couplings_of_isTightMeasureSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:34.434525+00:00
-- url     : https://prove2.me/submissions/6eff54c3-64f5-4bc7-8d76-68bbb19fd60e

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC

set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    {S : Set (Measure A)} {T : Set (Measure B)}
    (hS : IsTightMeasureSet S) (hT : IsTightMeasureSet T) :
    IsTightMeasureSet
      {γm : Measure (A × B) | γm.map Prod.fst ∈ S ∧ γm.map Prod.snd ∈ T} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS hT ⊢
  intro ε hε
  obtain ⟨K₁, hK₁c, hK₁⟩ := hS (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K₂, hK₂c, hK₂⟩ := hT (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨K₁ ×ˢ K₂, hK₁c.prod hK₂c, fun γm hγm => ?_⟩
  calc γm ((K₁ ×ˢ K₂)ᶜ)
      = γm ((K₁ᶜ ×ˢ univ) ∪ (univ ×ˢ K₂ᶜ)) := by rw [Set.compl_prod_eq_union]
    _ ≤ γm (K₁ᶜ ×ˢ univ) + γm (univ ×ˢ K₂ᶜ) := measure_union_le _ _
    _ = (γm.map Prod.fst) K₁ᶜ + (γm.map Prod.snd) K₂ᶜ := by
        rw [Set.prod_univ, Set.univ_prod,
          Measure.map_apply measurable_fst hK₁c.isClosed.measurableSet.compl,
          Measure.map_apply measurable_snd hK₂c.isClosed.measurableSet.compl]
    _ ≤ ε / 2 + ε / 2 := add_le_add (hK₁ _ hγm.1) (hK₂ _ hγm.2)
    _ = ε := ENNReal.add_halves ε
