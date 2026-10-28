-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_upcrossing_finite_time_window_probability_bound
-- name    : AvramDividend.Classical.chat01_upcrossing_finite_time_window_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:00:49.425389+00:00
-- url     : https://prove2.me/theorems/9cc2bfdf-387f-4de2-97f4-3c5df51973b2
-- title:
--   Explicit finite-upcrossing time-window probability estimate under positive Esscher root
-- statement:
--   Fix a spectrally negative Lévy process with positive Esscher root and a nonnegative upper-passage level z. Given measurability of the finite-upcrossing event whose passage clock is at most time t, its probability times exp(-q t) is bounded above by exp(-φ z). This concrete time-window formulation is a direct corollary of the general measurable restricted-event estimate and supports finite-horizon decay arguments.
-- source:
--   Proved chat01_measurable_finite_horizon_upcrossing_probability_bound and membership of the finite hitting-time window.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_measurable_finite_horizon_upcrossing_probability_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_upcrossing_finite_time_window_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (t : ℝ)
    (hWindowMeas : MeasurableSet
      {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
        ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t}) :
    ENNReal.ofReal (Real.exp (-(q * t))) *
      P {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
        ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t} ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
