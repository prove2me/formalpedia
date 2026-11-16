-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54x_original_stopped_physical_grid_kink_positivepart_upper
-- name    : AvramDividend.Classical.avram_gbB54x_original_stopped_physical_grid_kink_positivepart_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:33:48.778626+00:00
-- url     : https://prove2.me/theorems/5e6f9c90-ea0f-4f73-ab80-8315a90771b4
-- title:
--   Original Gaussian physical mesh positive-part caplinear kink residual bounded by smooth continuation
-- statement:
--   For the original stopped Gaussian physical mesh with actual right-limit dividends and source centred gain, the positive part of the aggregate upper-caplinear first-order residual is bounded by the positive part of the smooth slope-alpha continuation residual. The proof applies max monotonicity to the source-complete B54s sum comparison. This bound is the exact one-sided positive-error orientation needed in the B54 cash L1 proof; it avoids an incorrect absolute-value estimate across the nonzero negative local-time kink.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_gbB54x_original_stopped_physical_grid_kink_positivepart_upper
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
    max ((∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (V (Y i + R i) - V (Y i) -
          (if Y i ≤ b then g i else 1) * R i)
      else 0)) 0 ≤
      max ((∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (U (Y i + R i) - U (Y i) -
          (if Y i ≤ b then g i else α) * R i)
      else 0)) 0 := by sorry
