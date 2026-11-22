-- Prove2me | solution 1 for indepFrom_iff_indepSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:42.083186+00:00
-- url     : https://prove2.me/submissions/2ff02c1d-0fe9-476a-94cb-b80599dee518

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
open MeasurableSpace Measure
variable {s : Set Ω} {t t' : Set (Set Ω)}
theorem _root_.solution {P : Measure Ω} [IsZeroOrProbabilityMeasure P]
    {s : Set Ω} {t : Set (Set Ω)} (hs : MeasurableSet s) (ht : ∀ i ∈ t, MeasurableSet i) :
    IndepFrom s t P ↔ IndepSets {s} (generatePiSystem t) P := by
  rw [IndepFrom, ← generateFrom_generatePiSystem_eq (g := t)]
  constructor
  · intro h
    exact h.indepSets
  · intro h
    apply h.indep' _ _ (.singleton s) (isPiSystem_generatePiSystem _)
    · simpa
    · exact generatePiSystem_measurableSet ht
