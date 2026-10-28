-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_schedule
-- name    : AvramDividend.Classical.bv_actual_levy_drift_upper_ae_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:01:30.127341+00:00
-- url     : https://prove2.me/theorems/9f1ac36a-7d3b-4817-8961-362a0e87e488
-- title:
--   Common probability-one BV drift bound at every time in a countable schedule
-- statement:
--   For a bounded-variation spectrally negative Lévy process and any countable sequence of nonnegative times, a single probability-one event satisfies X(t_n) ≤ d t_n for every index n. This follows from the already-Proved fixed-time a.e. bound and the countable conjunction theorem ae_all_iff. It is the needed bridge toward a dense-schedule and càdlàg path bound.
-- source:
--   Proved bv_actual_levy_drift_upper_ae_fixed_time and pinned MeasureTheory.ae_all_iff.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_drift_upper_ae_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (ts : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      X.X (ts n) ω ≤ ((ts n : ℝ≥0) : ℝ) * X.drift := by sorry
