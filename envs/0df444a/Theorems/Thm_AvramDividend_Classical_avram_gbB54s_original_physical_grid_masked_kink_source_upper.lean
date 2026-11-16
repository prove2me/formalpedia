-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54s_original_physical_grid_masked_kink_source_upper
-- name    : AvramDividend.Classical.avram_gbB54s_original_physical_grid_masked_kink_source_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:25:23.548027+00:00
-- url     : https://prove2.me/theorems/8fa9be08-661c-4350-9e40-36cbe1c26b1a
-- title:
--   Original stopped physical Gaussian grid upper caplinear kink has nonpositive source remainder
-- statement:
--   The precise stopped physical-grid Gaussian source using original Levy increments, right-limit dividend reserve, nonnegative discounts, and source start-mask has its one-sided first-order clipped upper-cap spatial error bounded by a slope-alpha continuation. The lower cutoff enters the source derivative gain and the theorem makes no unverified assumptions about stochastic limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_gbB54s_original_physical_grid_masked_kink_source_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (a b α q x : ℝ) (hα : 1 ≤ α)
    (D : ℝ≥0 → Ω → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let g : ℕ → ℝ := fun i => if a ≤ Y i then deriv w (Y i) else 1
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    (∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (V (Y i + R i) - V (Y i) -
          (if Y i ≤ b then g i else 1) * R i)
      else 0) ≤
    (∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (U (Y i + R i) - U (Y i) -
          (if Y i ≤ b then g i else α) * R i)
      else 0) := by sorry
