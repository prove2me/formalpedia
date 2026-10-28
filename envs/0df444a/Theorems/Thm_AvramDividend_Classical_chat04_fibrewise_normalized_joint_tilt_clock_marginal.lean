-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_fibrewise_normalized_joint_tilt_clock_marginal
-- name    : AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_clock_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:41:59.535669+00:00
-- url     : https://prove2.me/theorems/5a7edbe3-504f-4d75-b207-21f84b4b1722
-- title:
--   A fibrewise-normalised time-dependent likelihood preserves the observation-clock distribution exactly
-- statement:
--   Let P be a path probability, η an observation-time probability on ℝ, and D(ω,t) jointly measurable and nonnegative with E_P D_t=1 for every t. The genuine joint measure (P⊗η).withDensity D has observation-time marginal exactly η, even though the path law conditional on time is tilted. This establishes that the external Exp(p) observation clock retains its exponential law after applying the time-dependent Esscher likelihood, a mathematically necessary step before any finite-rate Wiener–Hopf factorisation.
-- source:
--   Use measure extensionality on measurable sets B of ℝ. Expand `Measure.map Prod.snd` and `withDensity_apply`, rewrite the restricted joint density integral as an indicator integral, and apply `lintegral_prod_symm` to integrate first over paths P. The indicator of {t∈B} factors through the second coordinate, so fibrewise normalisation yields `B.indicator 1` integrated over η. Pinned `lintegral_indicator_const` evaluates this as η(B). All equalities hold for the true weighted product measure, not an assumed infinite-time tilted process.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_clock_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (hunit : ∀ t : ℝ, (∫⁻ ω, D (ω, t) ∂P) = 1) :
    Measure.map Prod.snd ((P.prod η).withDensity D) = η := by sorry
