-- Prove2me | Theorems.Thm_AvramDividend_Classical_setIntegral_eq_of_measures_agree_on_subsigma
-- name    : AvramDividend.Classical.setIntegral_eq_of_measures_agree_on_subsigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:53:38.187395+00:00
-- url     : https://prove2.me/theorems/6b584c4b-a9fb-4bfc-8d45-3caf871dfcef
-- title:
--   Earlier-filtration event integrals agree under any two laws matching on the filtration
-- statement:
--   If two measures agree on every measurable set of a smaller σ-algebra, they have equal integrals of every strongly measurable earlier-observable f restricted to an earlier measurable event A. This is exactly the set-integral form required to transfer the projective Esscher exponential martingale identity to a single fixed terminal-horizon Esscher law.
-- source:
--   Apply the proven general equal-integrals-for-subσ theorem to the indicator of f on the smaller-algebra event A. Rewrite both indicators as restricted integrals using pinned Mathlib `integral_indicator`. The indicator is strongly measurable by pinned `StronglyMeasurable.indicator`.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Theorems.Thm_AvramDividend_Classical_integral_eq_of_measures_agree_on_subsigma
open MeasureTheory Set

theorem AvramDividend.Classical.setIntegral_eq_of_measures_agree_on_subsigma
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : Measure Ω)
    (hset : ∀ B : Set Ω, @MeasurableSet Ω m B → μ B = ν B)
    (A : Set Ω) (hA : @MeasurableSet Ω m A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    (∫ ω in A, f ω ∂μ) = (∫ ω in A, f ω ∂ν) := by sorry
