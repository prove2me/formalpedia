-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
-- name    : AvramDividend.Classical.avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:01:26.42093+00:00
-- url     : https://prove2.me/theorems/64311951-a96a-4bf8-8765-56660f3faf66
-- title:
--   Canonical genuinely unmarked original random-grid cells satisfy simultaneous conull intrinsic Gaussian drift source decomposition
-- statement:
--   Under finite negative activity and the original global intrinsic truncated Gaussian residual and small-band compensated source limits, each genuinely jump-free cell of any finite ordered random physical grid satisfies, on one simultaneous conull original source event, the exact Lévy increment decomposition into intrinsic Gaussian residual and the small-negative-mark compensator drift. The selected jump-containing grid cells are defined by actual source left-limit jumps. This discharges the conull unmarked-cell Gaussian identity hypothesis required by the true ruin-clipped source mixed energy theorem; the original process and random grid are unchanged.
-- source:
--   Proved B159 original source jumpfree interval Gaussian identity plus exact original physical jump selector and countable-conull intersection.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (J : Ω → Finset ℕ)
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
      (R (t i ω) ω - R (s i ω) ω) +
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((t i ω - s i ω : ℝ≥0) : ℝ) := by sorry
