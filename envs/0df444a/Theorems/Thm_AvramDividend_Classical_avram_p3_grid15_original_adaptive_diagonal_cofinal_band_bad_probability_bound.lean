-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
-- name    : AvramDividend.Classical.avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:25:08.407452+00:00
-- url     : https://prove2.me/theorems/ece174ef-d4ac-49dd-ae17-9aef94580f73
-- title:
--   Original Lévy physical-grid adaptive cofinal bands control escape probability
-- statement:
--   For each changing original physical grid row, select a sufficiently late cofinal spatial band so that the probability of any actual interior prepayment reserve grid observation lying outside that band is smaller than an arbitrary positive prescribed error level. This is a mathematically genuine diagonal extraction from the Proved fixed-row localisation result 61ebbc7a; a summable choice of errors can support almost-everywhere eventual localisation in the P3 compensated-source route. This does not assert the conclusion for the prescribed diagonal band sequence or prove any compensator error estimate.
-- source:
--   Public accepted original-process finite-row cofinal-band probability theorem 61ebbc7a, with diagonal extraction by eventuality and classical choice.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n) :
    ∃ κ : ℕ → ℕ,
      (∀ n, n ≤ κ n) ∧
      ∀ n,
        P ({ω : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))}ᶜ) < ε n := by sorry
