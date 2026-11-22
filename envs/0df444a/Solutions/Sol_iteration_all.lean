-- Prove2me | solution 1 for iteration_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:42:44.495172+00:00
-- url     : https://prove2.me/submissions/3ea6beee-1854-48d3-bbe8-f24c56ada669

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_iteration

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    {t : Finset ι}
    (hx₁ : ∀ i, x i ≤ 1)
    (h : ∀ i : ι, ∀ S : Finset ι, i ∉ S → IndividualBound P A x i S) :
    ∏ j ∈ t, (1 - x j) ≤ P.real (⋂ j ∈ t, (A j)ᶜ) := by
  have : ∀ T ⊂ t, ∀ {i}, i ∉ T → IndividualBound P A x i T := by
    intro T hTt i hiT
    exact h i T hiT
  classical
  simpa using iteration (P := P) hA (t' := ∅) (by simp) hx₁ t (by simp) (by simp) this
