-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
-- name    : AvramDividend.Classical.avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:46:16.021675+00:00
-- url     : https://prove2.me/theorems/61ebbc7a-c762-4d9a-be6b-0921287339a6
-- title:
--   Original Lévy predictable prepayment reserve finite-row cofinal bands exhaust sample mass
-- statement:
--   For the original SpectrallyNegativeLevy source and actual dividend strategy, deterministic stopped-grid observations of the true strict left-limit reserve are measurable. Combining accepted original-source finite-horizon joint measurability (d8a9025e) with the fixed-row cofinal-band probability exhaustion theorem (a27bbe5c) shows the probability that any interior pre-jump sampled reserve escapes its cofinal spatial band tends to zero, at each fixed finite original physical row. This supplies a source-exact event component for original BV stopped-grid expected error localisation 0b2da5b3, without extra source-copy assumptions or claiming uniform integrability.
-- source:
--   Accepted original source d8a9025e plus new fixed-row probability exhaustion a27bbe5c; direct original grid/time/sample instantiation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (u : ℕ → ℕ → ℝ≥0) :
    Tendsto (fun k : ℕ =>
      P ({ω : Ω | ∀ i < n + 1,
        (0 < Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
          Icc (a k) (b k)}ᶜ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
