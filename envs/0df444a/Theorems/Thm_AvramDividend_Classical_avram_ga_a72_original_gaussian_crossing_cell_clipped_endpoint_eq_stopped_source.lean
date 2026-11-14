-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
-- name    : AvramDividend.Classical.avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:43:37.152445+00:00
-- url     : https://prove2.me/theorems/671b6729-24bb-4dca-ab5d-3f7aeb46f7f6
-- title:
--   Unique genuine Gaussian stop-straddling physical cell has clipped clock at rho and original stopped source spatial Taylor endpoint
-- statement:
--   For the true stopping-straddling original physical Gaussian grid cell whose start precedes rho but end crosses rho, the clipped spatial Taylor clock is exactly rho and the original actual source-dividend endpoint equals the true stopped source at rho with the prior dividend right limit.
-- source:
--   Original b0d9951c unique stop-straddling source spatial Taylor cell identity; distinguish from ga_a71 full pre-stop cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hstart : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hend : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ + Δ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    v i = s ∧ v (i + 1) = ρ ∧
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω =
        x + X.X ρ ω - rightLimit D s ω := by sorry
