-- Prove2me | solution 1 for isCompact_probabilityMeasure_couplings_toMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:00.659576+00:00
-- url     : https://prove2.me/submissions/2fdc2913-5327-4977-86d6-85c40bf888cd

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Theorems.Thm_probabilityMeasure_couplings_toMeasure_eq
import Theorems.Thm_isCompact_probabilityMeasure_couplings

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      (γ : Measure (A × B)).map Prod.fst = (mu : Measure A) ∧
      (γ : Measure (A × B)).map Prod.snd = (nu : Measure B)} := by
  rw [probabilityMeasure_couplings_toMeasure_eq]
  exact isCompact_probabilityMeasure_couplings mu nu
