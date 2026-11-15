-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
-- name    : AvramDividend.Classical.avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:48:34.036804+00:00
-- url     : https://prove2.me/theorems/3ef856d9-6759-4f3a-8059-a4a78cd38ff5
-- title:
--   Original Gaussian physical source cell is exactly affine through the upper interior clipping strip
-- statement:
--   For the genuine original physical Gaussian source X, dividend right limit D frozen at the left cell clock and interior caplinear payoff V_b, whenever the left and right source reserve states are strictly above b, the full-cell caplinear spatial payoff increment is exactly the original source Lévy increment X(s+Δ)-X(s). Hence the upper affine clipping strip creates no nonlinear spatial Taylor remainder on such full cells, preserving the exact physical source and right-payment bookkeeping needed for B54.
-- source:
--   Above b the interior clipping continuation V_b(z)=w(b)+z-b has unit slope. Subtract at the true source Y=x+X(s)-rightLimit D(s) and Z=x+X(s+Δ)-rightLimit D(s); cancel the fixed original rightDividend and caplinear constant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB66_original_caplinear_upper_strip_physical_cell_source_exact_affine
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
    b < Y → b < Z →
      V Z - V Y = X.X (s + Δ) ω - X.X s ω := by sorry
