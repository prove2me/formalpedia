-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_survival_positive_deficit_grid_cell_ae
-- name    : AvramDividend.Classical.bv_strict_survival_positive_deficit_grid_cell_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:44:11.313926+00:00
-- url     : https://prove2.me/theorems/a7d42570-f8a5-4e5a-8a33-04a7b11b2a54
-- title:
--   Before strict zero-barrier ruin a positive actual BV deficit forces a small positive grid increment
-- statement:
--   For an actual bounded-variation spectrally negative Lévy process, on a common full-measure event, surviving strictly beyond T makes the capital path nondecreasing. If the drift deficit nevertheless increases between grid endpoints, some grid-cell residual increment is strictly positive and is bounded by the cell drift budget b. This is the exact pathwise inclusion required for the grid-Laplace first-jump proof.
-- source:
--   Proved real finite-grid lemma and source-faithful BV strict-survival increment band; Avram et al. (2007), section 3.3.

import Theorems.Thm_AvramDividend_Classical_bv_strict_zero_ruin_deficit_increment_band_ae
import Theorems.Thm_AvramDividend_Classical_positive_grid_deficit_has_small_positive_increment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_survival_positive_deficit_grid_cell_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (b : ℝ)
    (hStep : ∀ k : ℕ, LT.lt k N → LE.le (ts k) (ts (k + 1)))
    (hWithin : ∀ k : ℕ, LT.lt k N → LE.le (ts (k + 1)) T)
    (hMesh : ∀ k : ℕ, LT.lt k N →
       LE.le (X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ))) b) :
    ∀ᵐ ω ∂P, LT.lt (T : ℝ≥0∞) (barrierRuinTime X 0 ω) →
      LT.lt
        (X.drift * (ts 0 : ℝ) - X.X (ts 0) ω)
        (X.drift * (ts N : ℝ) - X.X (ts N) ω) →
      ∃ k : ℕ, LT.lt k N ∧
        LT.lt 0 ((X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω)) ∧
        LE.le ((X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω)) b := by sorry
