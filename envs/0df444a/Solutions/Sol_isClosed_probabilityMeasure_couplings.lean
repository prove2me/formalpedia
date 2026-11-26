-- Prove2me | solution 1 for isClosed_probabilityMeasure_couplings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:33.636233+00:00
-- url     : https://prove2.me/submissions/20d9c138-4689-4f46-8fb0-d86f8283fdd7

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
    IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu ∧ γ.map measurable_snd.aemeasurable = nu} := by
  have hfst : IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu} :=
    isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_fst)
  have hsnd : IsClosed {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_snd.aemeasurable = nu} :=
    isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_snd)
  exact hfst.inter hsnd
