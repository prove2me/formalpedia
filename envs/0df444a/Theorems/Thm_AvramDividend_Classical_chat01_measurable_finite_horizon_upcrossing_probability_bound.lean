-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_measurable_finite_horizon_upcrossing_probability_bound
-- name    : AvramDividend.Classical.chat01_measurable_finite_horizon_upcrossing_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:52:09.133995+00:00
-- url     : https://prove2.me/theorems/b909c8b2-8588-42a6-848d-29a7a59a96e7
-- title:
--   Esscher exponential probability bound for measurable finite-horizon upcrossing events
-- statement:
--   For any measurable restricted first-upcrossing event whose passage time is at most a fixed horizon t, the probability of that event, multiplied by its deterministic discount exp(-q t), is bounded above by the positive Esscher-root tail exp(-φ z). This converts a pathwise stopping-clock estimate into a quantitative probability bound. It is designed for passage-time grid arguments, lower killing, and limiting fixed-horizon events.
-- source:
--   Import the Proved finite-horizon upcrossing discount bound and use MeasureTheory.lintegral_indicator_const with MeasurableSet A.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_discount_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_measurable_finite_horizon_upcrossing_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) :
    ENNReal.ofReal (Real.exp (-(q * t))) * P A ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
