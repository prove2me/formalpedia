-- Prove2me | solution 1 for localLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:34.167642+00:00
-- url     : https://prove2.me/submissions/f35adb14-6b99-492a-a105-42a948e3bc00

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_iteration_all
import Theorems.Thm_individualBound

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution [Fintype ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i ≤ 1)
    (h : lopsidedCondition P A N)
    (hAx : ∀ i, P.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ P.real (⋂ i, (A i)ᶜ) := by
  have : ∀ i, ∀ S, i ∉ S → IndividualBound P A x i S := by
    intro i S hiS
    classical
    exact individualBound hA h hx₀ hx₁ hAx hiS
  simpa using iteration_all hA hx₁ this (t := univ)
