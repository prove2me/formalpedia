-- Prove2me | solution 1 for probabilityMeasure_couplings_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:05.445057+00:00
-- url     : https://prove2.me/submissions/59e952cc-1b8e-430c-a8a8-efe7990cd732

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact

set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
omit [TopologicalSpace A] [PolishSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [BorelSpace B]
theorem _root_.solution
    (mu : ProbabilityMeasure A) (nu : ProbabilityMeasure B) :
    {γ : ProbabilityMeasure (A × B) |
      γ.map measurable_fst.aemeasurable = mu ∧
      γ.map measurable_snd.aemeasurable = nu}.Nonempty :=
  ⟨mu.prod nu, ProbabilityMeasure.map_fst_prod mu nu, ProbabilityMeasure.map_snd_prod mu nu⟩
