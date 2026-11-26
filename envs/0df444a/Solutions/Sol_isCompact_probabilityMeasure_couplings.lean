-- Prove2me | solution 1 for isCompact_probabilityMeasure_couplings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:50.027128+00:00
-- url     : https://prove2.me/submissions/6bf3234b-424f-47f1-ba8f-3cc4f5c2064f

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Theorems.Thm_isClosed_probabilityMeasure_couplings
import Theorems.Thm_isTightMeasureSet_probabilityMeasure_couplings

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    IsCompact {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu ∧ γ.map measurable_snd.aemeasurable = nu} := by
  have hcompact : IsCompact (closure {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu ∧ γ.map measurable_snd.aemeasurable = nu}) :=
    isCompact_closure_of_isTightMeasureSet
      (isTightMeasureSet_probabilityMeasure_couplings mu nu)
  rwa [(isClosed_probabilityMeasure_couplings mu nu).closure_eq] at hcompact
