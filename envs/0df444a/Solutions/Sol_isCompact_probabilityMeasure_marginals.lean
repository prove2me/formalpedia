-- Prove2me | solution 1 for isCompact_probabilityMeasure_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:04.937458+00:00
-- url     : https://prove2.me/submissions/c2a9e378-17ff-4857-8285-3d3af7ead016

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Theorems.Thm_isCompact_probabilityMeasure_couplings_toMeasure

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution (m : Measure A) (n : Measure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      (γ : Measure (A × B)).map Prod.fst = m ∧ (γ : Measure (A × B)).map Prod.snd = n} := by
  by_cases hm : IsProbabilityMeasure m
  · by_cases hn : IsProbabilityMeasure n
    · exact isCompact_probabilityMeasure_couplings_toMeasure ⟨m, hm⟩ ⟨n, hn⟩
    · have hempty : {γ : ProbabilityMeasure (A × B) |
          (γ : Measure (A × B)).map Prod.fst = m ∧
          (γ : Measure (A × B)).map Prod.snd = n} = ∅ := by
        ext γ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ h2
        exact hn (h2 ▸ (γ : Measure (A × B)).isProbabilityMeasure_map
          measurable_snd.aemeasurable)
      rw [hempty]
      exact isCompact_empty
  · have hempty : {γ : ProbabilityMeasure (A × B) |
        (γ : Measure (A × B)).map Prod.fst = m ∧
        (γ : Measure (A × B)).map Prod.snd = n} = ∅ := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 _
      exact hm (h1 ▸ (γ : Measure (A × B)).isProbabilityMeasure_map
        measurable_fst.aemeasurable)
    rw [hempty]
    exact isCompact_empty
