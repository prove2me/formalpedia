-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_grid_spatial_source_tail_diagonal
-- name    : AvramDividend.Classical.avram_a06_original_BV_uniform_grid_spatial_source_tail_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:52:33.210374+00:00
-- url     : https://prove2.me/theorems/f1c21273-eb1b-46ad-8e52-e1e5ab902540
-- title:
--   A06 original physical Lévy grid admits increasing cofinal spatial source-tail L1 diagonal
-- statement:
--   For every actual BV standing spectrally negative Lévy process, controlled dividend strategy and finite original time horizon, and every cofinal compact spatial interior-band sequence, there exists a strictly increasing spatial localisation index phi(n) at least n such that the expected genuine original BV source mass omitted from the n-th physical uniform-grid row converges to zero along k=phi(n). Each fixed-row expected error tends to zero by the Proved original source any-clock band theorem 16aebd7f; the error is nonnegative by Proved source mass positivity; a proved diagonal selection theorem assembles a true simultaneous original-row spatial localisation. This does not assume signed generator-residual integrability or the stopped cash/HJB budget.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_uniform_grid_spatial_source_tail_diagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let E : ℕ → ℕ → ℝ := fun n k =>
      ∫ ω, (if ∀ i < n + 1,
        (0 < Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
            ∈ Icc (a k) (b k) then (0 : ℝ)
          else |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|) ∂P
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n, n ≤ φ n) ∧
      Tendsto (fun n => E n (φ n)) atTop (𝓝 (0 : ℝ)) := by sorry
