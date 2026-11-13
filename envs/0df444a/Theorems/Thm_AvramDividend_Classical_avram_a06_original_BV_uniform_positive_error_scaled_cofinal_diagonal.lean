-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_positive_error_scaled_cofinal_diagonal
-- name    : AvramDividend.Classical.avram_a06_original_BV_uniform_positive_error_scaled_cofinal_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:18:26.766466+00:00
-- url     : https://prove2.me/theorems/46dc9978-4784-4ef8-9058-f8777ad2bb76
-- title:
--   Original BV physical grid positive error vanishes even after multiplication by cell count
-- statement:
--   For the exact original standing spectrally negative Lévy process, actual controlled dividend strategy, and any finite horizon, a strictly increasing cofinal spatial localisation can be chosen so that the mean positive source error on the n-th uniform physical grid row is o(1/(n+1)). Consequently, an n+1-cell accumulated error dominated by the row-wise source envelope tends to zero. This strengthens the already Proved unscaled A06 physical error selector, using the quantitative diagonal theorem and original BV source envelope. It leaves the stochastic cash/HJB identity as a separate obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_uniform_positive_error_scaled_cofinal_diagonal
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
      (∀ n, Integrable (fun ω => max (Err n (κ n) ω) 0) P) ∧
      Tendsto (fun (n : ℕ) => ((n : ℝ) + 1) * (∫ ω, max (Err n (κ n) ω) 0 ∂P))
        atTop (𝓝 (0 : ℝ)) := by sorry
