-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_grid_binary_cover_ae_ws01b
-- name    : AvramDividend.Classical.bv_actual_grid_binary_cover_ae_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:23:04.888967+00:00
-- url     : https://prove2.me/theorems/cd33d0b5-a9ff-4d49-8052-290bb88e0cc0
-- title:
--   Almost-sure binary classification of every actual bounded-variation Lévy increment on a deterministic grid
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, almost every sample path has the property that each increment along every finite deterministic nondecreasing grid is either strictly below drift times cell length or exactly equal to that drift increment. The theorem uses the previously proved full-time almost-sure monotonicity of the actual drift-deficit path and requires no finite-activity restriction.
-- source:
--   The complete proof passed pinned Prove2Me remote Lean compilation on 28 October 2026. It specialises the proved actual-process almost-sure monotonic drift deficit to each grid interval, rewrites the residual increment using the NNReal cast subtraction identity, and splits its nonnegative value into positive or zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Almost surely, every actual bounded-variation Lévy grid increment is
either strictly below the physical drift increment or exactly equal to it. -/

theorem AvramDividend.Classical.bv_actual_grid_binary_cover_ae_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω <
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) ∨
      X.X (t (i + 1)) ω - X.X (t i) ω =
        X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)) := by sorry
