-- Prove2me | Theorems.Thm_AvramDividend_Classical_setIntegral_eq_of_ambient_measures_agree_on_subsigma
-- name    : AvramDividend.Classical.setIntegral_eq_of_ambient_measures_agree_on_subsigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:09:38.39604+00:00
-- url     : https://prove2.me/theorems/bd6743a8-5ac7-43d3-becb-9932411f530a
-- title:
--   Ambient measures agreeing on a sub-sigma-algebra have equal earlier-event integrals
-- statement:
--   Let m be a sub-σ-algebra of ambient m0. Two *ambient-m0* measures μ,ν that agree on every m-measurable event have equal real Bochner integrals over any m-measurable event A of any strongly m-measurable function f. Unlike a previous polymorphic presentation, the measure types are explicitly fixed as `@Measure Ω m0`; this is essential for genuine finite Esscher laws defined on the ambient Lévy path space.
-- source:
--   Construct μ.trim hm and ν.trim hm, both as measures over the smaller σ-algebra m; prove equality by measure extensionality using `trim_measurableSet_eq`. Transfer the indicator integral through `integral_trim` under each original ambient measure, and rewrite `integral_indicator` back to restricted integrals. Explicit `@Measure Ω m0` prevents implicit measure space elaboration from silently selecting m.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.setIntegral_eq_of_ambient_measures_agree_on_subsigma
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : @Measure Ω m0)
    (hset : ∀ B : Set Ω, @MeasurableSet Ω m B → μ B = ν B)
    (A : Set Ω) (hA : @MeasurableSet Ω m A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    (∫ ω in A, f ω ∂μ) = (∫ ω in A, f ω ∂ν) := by sorry
