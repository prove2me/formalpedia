-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_all_right_clocks_killed_terminal_tendsto
-- name    : AvramDividend.Classical.avram_wave8_20_original_all_right_clocks_killed_terminal_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:28:13.465086+00:00
-- url     : https://prove2.me/theorems/dc9f7b01-07f5-4855-9e6c-b08edca35533
-- title:
--   Exact original strict-ruin killed postrightpayment HJB terminal converges from right at all finite physical times
-- statement:
--   For every source sample path and finite physical time, the exact strict-survival killed post-rightpayment positive candidate continuation converges along clocks approaching from the right to its exact killed value at that time, including first ruin.
-- source:
--   Original Avram Proposition 4(i) strict ruinTime and postrightpayment discounted positive-part candidate. An inline pre-ruin derivation combines already Proved source HJB postpayment rightcontinuity 634baba4 and eventual strict survival f77d306f with continuous discount and positive part. At and after ruin, already Proved c07eabc1 annihilates the terminal at all right clocks. Only Proved source imports are used. Exact limit can feed bounded terminal DCT 274b6f2c, without circular stochastic inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_all_right_clocks_killed_terminal_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (𝓝 t))
    (hRight : ∀ n, t ≤ τ n) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) Filter.atTop
      (𝓝 (if (t : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω))
        else 0)) := by sorry
