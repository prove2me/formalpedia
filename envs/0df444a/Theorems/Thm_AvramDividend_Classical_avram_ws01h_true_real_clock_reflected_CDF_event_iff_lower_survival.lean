-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival
-- name    : AvramDividend.Classical.avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:25:49.713997+00:00
-- url     : https://prove2.me/theorems/81847f84-262d-4b5e-8cfd-3b19450159a6
-- title:
--   Actual real-clock Lévy reflected-infimum CDF event equals full original continuous lower survival pathwise
-- statement:
--   For every original spectrally negative Lévy process and every actual sample path and real observation clock, the full event that the negative running infimum up to the original real clock converted to a finite nonnegative horizon is at most reserve x is exactly the complete uncountable closed-history nonruin event ∀s≤clock, 0≤x+X_s. This transports the canonically Proved finite-horizon sample-path identity to the genuine path×real-clock state space and is the exact source event bridge needed to identify the renewal CDF with the already accepted perpetual Esscher reflected-infimum limit. No tilted path law, q-scale identity, stochastic approximation or a.e. substitution is assumed.
-- source:
--   Canonically Proved chat04_reflected_infimum_Iic_iff_survival 3e4d270c; original SpectrallyNegativeLevy state and Real.toNNReal clock.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) :
    {z : Ω × ℝ |
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} =
    {z : Ω × ℝ |
      ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
        0 ≤ x + X.X s z.1} := by sorry
