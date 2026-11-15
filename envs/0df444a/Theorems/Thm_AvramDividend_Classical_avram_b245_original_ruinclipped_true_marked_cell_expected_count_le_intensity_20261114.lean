-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b245_original_ruinclipped_true_marked_cell_expected_count_le_intensity_20261114
-- name    : AvramDividend.Classical.avram_b245_original_ruinclipped_true_marked_cell_expected_count_le_intensity_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:28:33.152049+00:00
-- url     : https://prove2.me/theorems/07d88aef-6835-4d6e-8df3-41352fdd6b3a
-- title:
--   Actual stopped physical negative-jump occupied-cell expected count bounded by horizon times original Lévy intensity
-- statement:
--   On the original finite-negative-activity spectrally negative Lévy probability space, the expectation of the number of distinct physically jump-occupied cells on the random grid stopped at a bounded right-continuous stopping time σ cannot exceed n ν((−∞,0)). The count is genuinely physical, the grid never crosses the stopped time and no auxiliary Poisson model is used. This explicit expectation estimate provides a deterministic uniform integrability budget for ruin-clipped marked-cell errors.
-- source:
--   B243 or B244 original occupied-cell measurable integrable and almost-sure negative physical count bound, plus Proved JA35 original marked negative real-count first moment identity, integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b245_original_ruinclipped_true_marked_cell_expected_count_le_intensity_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    (∫ ω, ((marked ω).card : ℝ) ∂P) ≤
      ((n : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
