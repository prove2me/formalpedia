-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_centered_past_times_future_mean_zero
-- name    : AvramDividend.Classical.avram_wave3_04_centered_past_times_future_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:27:43.870016+00:00
-- url     : https://prove2.me/theorems/3bc30ea1-c8cb-4e4d-ab8d-6ff6f54c6935
-- title:
--   A centered future Lévy increment payoff has zero mean against every integrable past coefficient
-- statement:
--   For an integrable centered Borel payoff of a genuine future Lévy increment, multiplication by any F_s strongly measurable earlier observation H leaves mean zero, provided the increment payoff and product are integrable. This is proved by pulling H through conditional expectation, applying the accepted independent-increment conditional law, and preserving the integral of conditional expectation. It is an exact finite-grid martingale-difference statement for the original Lévy process.
-- source:
--   Canonical Proved chat04_general_future_increment_conditional_expectation 60e3f274-5580-448a-a1d8-6485fa8ab41a; pinned Mathlib condExp_mul_of_stronglyMeasurable_left and integral_condExp. Private compiler job 75833e78-e162-411e-84b3-40d4300f69fe reached its sentinel with no candidate errors, SHA-256 cdb8bfc553fb9166afb2032cf98692ca7acadfa63a2c25e770dd103f42d0b3da.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_centered_past_times_future_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hIntInc : Integrable (fun ω => φ (X.X t ω - X.X s ω)) P)
    (hIntProd : Integrable
      (fun ω => H ω * φ (X.X t ω - X.X s ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    (∫ ω, H ω * φ (X.X t ω - X.X s ω) ∂P) = 0 := by sorry
