-- Prove2me | solution 1 for isTightMeasureSet_probabilityMeasure_couplings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:52.695805+00:00
-- url     : https://prove2.me/submissions/fa209aed-514a-4e02-8835-325f12aa9c94

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Theorems.Thm_probabilityMeasure_map_eq_iff
import Theorems.Thm_isTightMeasureSet_couplings

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsTightMeasureSet {((γ : ProbabilityMeasure (A × B)) : Measure (A × B)) |
      γ ∈ {γ' : ProbabilityMeasure (A × B) |
        γ'.map measurable_fst.aemeasurable = mu ∧
        γ'.map measurable_snd.aemeasurable = nu}} := by
  refine (isTightMeasureSet_couplings mu nu).subset ?_
  rintro x ⟨γ, ⟨h₁, h₂⟩, rfl⟩
  exact ⟨(probabilityMeasure_map_eq_iff γ mu measurable_fst).1 h₁,
    (probabilityMeasure_map_eq_iff γ nu measurable_snd).1 h₂⟩
