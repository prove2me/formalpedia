-- Prove2me | solution 1 for measurableSet_couplings_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:34.164547+00:00
-- url     : https://prove2.me/submissions/da6df762-184f-44fa-b794-677c51e2e731

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Theorems.Thm_isClosed_couplings_hit
import Theorems.Thm_IsOpen_exists_iUnion_isClosed_of_pseudoMetrizable

set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    {mPA : MeasurableSpace (ProbabilityMeasure A)}
    [BorelSpace (ProbabilityMeasure A)]
    {mPB : MeasurableSpace (ProbabilityMeasure B)}
    [BorelSpace (ProbabilityMeasure B)]
    {U : Set (ProbabilityMeasure (A × B))} (hU : IsOpen U) :
    MeasurableSet {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ U, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by
  obtain ⟨C, hCclosed, rfl⟩ := hU.exists_iUnion_isClosed_of_pseudoMetrizable
  have hsplit : {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ ⋃ n, C n, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)}
      = ⋃ n, {p : ProbabilityMeasure A × ProbabilityMeasure B |
        ∃ γ ∈ C n, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
          (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨γ, ⟨n, hγn⟩, hmarg⟩
      exact ⟨n, γ, hγn, hmarg⟩
    · rintro ⟨n, γ, hγn, hmarg⟩
      exact ⟨γ, ⟨n, hγn⟩, hmarg⟩
  rw [hsplit]
  exact MeasurableSet.iUnion fun n =>
    (isClosed_couplings_hit (hCclosed n)).measurableSet
