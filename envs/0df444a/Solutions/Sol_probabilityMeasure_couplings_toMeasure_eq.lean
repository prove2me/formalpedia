-- Prove2me | solution 1 for probabilityMeasure_couplings_toMeasure_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:47.402168+00:00
-- url     : https://prove2.me/submissions/83f6ab52-ade4-40f8-b31f-35c0749a1f07

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Theorems.Thm_probabilityMeasure_map_eq_iff

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
        (γ : Measure (A × B)).map Prod.fst = (mu : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (nu : Measure B)}
      = {γ : ProbabilityMeasure (A × B) |
          γ.map measurable_fst.aemeasurable = mu ∧
          γ.map measurable_snd.aemeasurable = nu} := by
  ext γ
  exact and_congr (probabilityMeasure_map_eq_iff γ mu measurable_fst).symm
    (probabilityMeasure_map_eq_iff γ nu measurable_snd).symm
