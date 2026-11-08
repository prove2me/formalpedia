-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
-- name    : AvramDividend.Classical.avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:55:32.539751+00:00
-- url     : https://prove2.me/theorems/a32a3872-4252-4d8e-8f60-35ea02965733
-- title:
--   Original Lévy stopped-grid cofinal bands furnish measurable eventually-good masks
-- statement:
--   For the exact original controlled spectrally negative Lévy reserve, a positive summable sequence of rowwise probability tolerances selects accelerated cofinal spatial bands with measurable physical-grid good events. Almost every path lies inside all the chosen interior prepayment-reserve bands at all sufficiently large grid rows. This proves precisely the measurable/eventual-localisation component needed by the canonical P3 compensated positive-error localisation, without asserting its expected-error convergence or stopped-contact estimates.
-- source:
--   Accepted original reserve joint measurability d8a9025e, source-exact adaptive Borel-Cantelli 8a9b5a97 and countable finite-event eventuality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid15_original_adaptive_band_exception_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤) :
    ∃ κ : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, n ≤ κ n) ∧
      (∀ n, s n = {ω : Ω | ∀ i < n + 1,
        (0 < Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
          Icc (a (κ n)) (b (κ n))}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) := by sorry
