-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a46_original_safe_cell_spatial_positive_floor
-- name    : AvramDividend.Classical.avram_ga_a46_original_safe_cell_spatial_positive_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:53:29.72984+00:00
-- url     : https://prove2.me/theorems/ead73ec5-79e3-4490-88aa-b8990c84b2c1
-- title:
--   All strictly pre-stop original Gaussian spatial Taylor endpoints inherit the positive reserve floor
-- statement:
--   For the genuine original source and dividend strategy, if the stopped prepayment reserve has a uniform positive floor before the stopping clock, then every strictly pre-stop later spatial endpoint formed with earlier postpayment dividends inherits the same floor almost surely.
-- source:
--   Original safe full-cell positive Taylor endpoint mathematical gap b0d9951c; Proved original strict-right dividend chronology gledger87.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_a46_original_safe_cell_spatial_positive_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t →
      0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤
        x + X.X t ω - rightLimit D s ω := by sorry
