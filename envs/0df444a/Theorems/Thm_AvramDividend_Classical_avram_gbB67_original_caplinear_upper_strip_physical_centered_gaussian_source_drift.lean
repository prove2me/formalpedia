-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
-- name    : AvramDividend.Classical.avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:57:11.100587+00:00
-- url     : https://prove2.me/theorems/f3c64b5e-ed90-4bf5-9bec-d2c6b649a157
-- title:
--   Original physical upper-strip clipped Gaussian spatial source minus centred increment equals its exact physical drift
-- statement:
--   For genuine original Gaussian Lévy process X, actual physical mesh and dividend rightLimit D frozen at cell start, when both source spatial reserve endpoints lie in the affine upper clipping strip, the interior caplinear test payoff spatial increment minus the true centred Gaussian source increment is exactly Δ X.c. This proves the exact deterministic cell drift term on the upper strip, matching the positive-drift occupation charge in B54 without arbitrary stochastic or payoff substitutions.
-- source:
--   Proved B66 exact upper affine caplinear spatial source identity, followed by subtracting the original physical centred increment X(s+Δ)-X(s)-Δ X.c and cancellation of the raw source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let centred : ℝ :=
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    b < Y → b < Z →
      V Z - V Y - centred = (Δ : ℝ) * X.c := by sorry
