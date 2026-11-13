-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_uniform_grid_weighted_source_tail_diagonal
-- name    : AvramDividend.Classical.avram_a06_original_BV_uniform_grid_weighted_source_tail_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:29:25.667198+00:00
-- url     : https://prove2.me/theorems/0b6a66b2-9fea-4102-a30b-9968556e511b
-- title:
--   A06 original physical BV mesh weighted exceptional-band source mass has vanishing diagonal mean
-- statement:
--   Given the original spectrally negative Lévy source, admissible dividends, arbitrary finite horizon, any physical prepayment reserve grid, cofinal compact interior bands and any nonnegative grid-row dependent coefficient L(n), choose strictly increasing spatial band indices φ(n) at least n so that the expected original BV source mass on omitted spatial events, multiplied by 1+L(n), converges to zero. This is genuine original-source localisation with nonuniform derivative or Lipschitz bounds; no signed HJB residual global integrability is assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_cofinal_weighted_spatial_error_diagonal
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_uniform_grid_weighted_source_tail_diagonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n) :
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
      Tendsto (fun n => (1 + L n) * E n (φ n)) atTop (𝓝 (0 : ℝ)) := by sorry
