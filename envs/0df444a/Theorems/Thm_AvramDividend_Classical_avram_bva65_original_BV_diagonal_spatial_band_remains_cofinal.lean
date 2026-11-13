-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva65_original_BV_diagonal_spatial_band_remains_cofinal
-- name    : AvramDividend.Classical.avram_bva65_original_BV_diagonal_spatial_band_remains_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:10:31.165363+00:00
-- url     : https://prove2.me/theorems/1b327205-5ce5-4539-a97e-fa203f81c695
-- title:
--   Original BV positive physical-row error diagonal retains cofinal interior band exhaustion
-- statement:
--   For the same original spectrally negative Levy process and admissible dividend D, select the positive expected spatial-error diagonal kappa(n) and additionally establish that selected compact interior bands a(kappa(n)),b(kappa(n)) still exhaust every strictly interior reserve eventually. This supplies the exact cofinality needed to invoke the existing centred-compensated source theorem on the diagonalised physical grid. No finite-activity assumption or generator global L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_positive_error_cofinal_diagonal
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva65_original_BV_diagonal_spatial_band_remains_cofinal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let Err : ℕ → ℕ → Ω → ℝ := fun n k ω =>
      if ∀ i < n + 1,
        (0 < Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
            ∈ Icc (a k) (b k) then (0 : ℝ)
          else |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a (κ n)) (b (κ n))) ∧
    (∀ n, Integrable (fun ω => max (Err n (κ n) ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n (κ n) ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
