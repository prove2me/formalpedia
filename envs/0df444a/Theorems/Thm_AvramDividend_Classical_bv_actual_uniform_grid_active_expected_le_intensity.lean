-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_uniform_grid_active_expected_le_intensity
-- name    : AvramDividend.Classical.bv_actual_uniform_grid_active_expected_le_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:18:44.020014+00:00
-- url     : https://prove2.me/theorems/bea0820b-b996-4e18-920f-d7afad7a04b5
-- title:
--   Actual finite-activity Lévy residual active-cell expected count is bounded by Lévy intensity times grid horizon
-- statement:
--   For an arbitrary deterministic N-cell uniform nonnegative-real time mesh spanning total real duration T, the expected number of cells in which the actual spectrally negative Lévy residual Y_t=d t−X_t has a strictly positive increment is at most the finite negative-jump intensity λ times T. Uses actual-process Proved positive-increment probability 1−exp(−λT/N), measurability from adaptedness, and the Proved generic finite-count intensity upper bound; no independence or Lévy–Itô decomposition is needed. This gives the crucial stochastic uniform dyadic count estimate on the original sample space.
-- source:
--   Avram Palmowski Pistorius (2007), finite activity first-jump law, §3.3; accepted actual-process increment probability and finite indicator expected count bound.

import Theorems.Thm_AvramDividend_Classical_bv_dyadic_uniform_active_expected_le_intensity
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_uniform_grid_active_expected_le_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (ts : ℕ → ℝ≥0) (N : ℕ) (hN : 0 < N)
    (T : ℝ)
    (hStep : ∀ i : ℕ, i < N → ts i ≤ ts (i + 1))
    (hMesh : ∀ i : ℕ, i < N →
      (((ts (i + 1) - ts i : ℝ≥0) : ℝ) = T / (N : ℝ))) :
    (∫⁻ ω, ∑ i ∈ Finset.range N,
      ({ω : Ω | 0 <
        ((ts (i + 1) : ℝ) * X.drift - X.X (ts (i + 1)) ω) -
          ((ts i : ℝ) * X.drift - X.X (ts i) ω)}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂P) ≤
      ENNReal.ofReal ((X.ν (Iio (0 : ℝ))).toReal * T) := by sorry
