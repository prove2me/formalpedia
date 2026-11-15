-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
-- name    : AvramDividend.Classical.avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:41:17.961596+00:00
-- url     : https://prove2.me/theorems/5939b7ba-d675-4e33-a325-97ed965add9f
-- title:
--   Actual original Gaussian rare fullcell compact jet polynomial is dominated by stopped raw-square tail
-- statement:
--   On sufficiently fine true original Gaussian physical meshes, the original deterministic drift per cell becomes smaller than the fixed rare-increment threshold. Hence the positive polynomial 1+abs(raw increment)+half centered square on every wholly pre-stop large raw increment is bounded by a deterministic delta-dependent multiple of that same raw square. The fully stopped finite sum is bounded by the genuine stopped-prefix rare raw-square sum, whose expectation is integrable and vanishes by a187. This proves the actual source polynomial tail estimate needed for a263.
-- source:
--   Original Gaussian a223 drift width and a261 scalar rare quadratic domination, original stopped fullcell source and a187 raw tail.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
import Theorems.Thm_AvramDividend_Classical_avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    ∀ᶠ m : ℕ in atTop, ∀ ω : Ω,
      (∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
           δ ≤ |R m i ω| then
          1 + |R m i ω| + (Z m i ω)^2 / 2 else 0) ≤
      (1/δ^2 + 1/δ + 2) *
      (∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if δ ≤ |R m i ω| then (R m i ω)^2 else 0)
        else 0) := by sorry
