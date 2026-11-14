-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
-- name    : AvramDividend.Classical.avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:43:34.855429+00:00
-- url     : https://prove2.me/theorems/abb433a7-9f5e-4b51-a228-1908c73b6663
-- title:
--   Every genuinely pre-stop full original Gaussian physical grid cell has exact unclipped source times and postdividend Taylor endpoint
-- statement:
--   On the genuine original process X, dividend strategy D and random stop rho, each physical Gaussian uniform mesh cell ending no later than rho has clipped start and end clocks equal the deterministic physical endpoints and its actual spatial source Taylor endpoint exactly matches the original full-cell source.
-- source:
--   Original b0d9951c safe full-cell source Taylor mesh versus stopped clipped v grid; direct application of positive compact and Lindeberg lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hfull : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ + Δ ≤ ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    v i = s ∧
      v (i + 1) = s + Δ ∧
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω =
        x + X.X (s + Δ) ω - rightLimit D s ω := by sorry
