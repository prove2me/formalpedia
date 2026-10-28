-- Prove2me | Theorems.Thm_AvramDividend_Classical_integral_eq_of_measures_agree_on_subsigma
-- name    : AvramDividend.Classical.integral_eq_of_measures_agree_on_subsigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:56:01.873334+00:00
-- url     : https://prove2.me/theorems/08922702-ce4f-4067-bf40-5f467e88512c
-- title:
--   Measures agreeing on all events in a smaller sigma algebra integrate its measurable observables equally
-- statement:
--   Let m be a sub-σ-algebra of the ambient measurable space. If two measures μ and ν agree on every m-measurable set, then they assign the same real Bochner integral to every strongly m-measurable real observable f. This theorem transfers projective Esscher consistency on earlier-filtration events into equality of earlier-observable expectations under different finite-horizon Esscher measures.
-- source:
--   By extensionality on all m-measurable sets, use `trim_measurableSet_eq` to prove equality of the two trimmed measures μ.trim m and ν.trim m. Then use pinned `integral_trim` for any strongly m-measurable real function and rewrite equality of trimmed measures. Crucially no integrability assumption is needed to state equality of the Bochner integrals (nonintegrable cases are still equal by the integral definition).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Trim
open MeasureTheory

theorem AvramDividend.Classical.integral_eq_of_measures_agree_on_subsigma
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : Measure Ω)
    (hset : ∀ A : Set Ω, @MeasurableSet Ω m A → μ A = ν A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    (∫ ω, f ω ∂μ) = (∫ ω, f ω ∂ν) := by sorry
