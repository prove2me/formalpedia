-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB69_original_physical_gaussian_caplinear_discounted_spatial_product_rule_cell
-- name    : AvramDividend.Classical.avram_gbB69_original_physical_gaussian_caplinear_discounted_spatial_product_rule_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:12:28.865496+00:00
-- url     : https://prove2.me/theorems/f3aec0ba-3229-4947-856f-acc5765283a9
-- title:
--   Original finite-cap Gaussian physical stopped cell exact discounted caplinear spatial product rule
-- statement:
--   On each genuine original physical Gaussian source cell, with original pre-right-dividend reserve Y and spatial endpoint Z freezing the actual rightLimit D at its cell start, the discounted caplinear potential increment equals the discounted original spatial source increment plus the exact temporal discount increment times the predividend endpoint potential. This is the precise physical-cell product rule connecting unweighted signed Stieltjes cash telescoping to the discounted Gaussian generator and martingale coefficients of B54.
-- source:
--   Exact scalar product-rule algebra using the original Lévy source X, original rightLimit D(s), physical mesh delta and actual interior clipped payoff V_b. No artificial stopping clock or global C2 hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB69_original_physical_gaussian_caplinear_discounted_spatial_product_rule_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) * V Z -
      Real.exp (-(q * (s : ℝ))) * V Y =
    Real.exp (-(q * (s : ℝ))) * (V Z - V Y) +
      (Real.exp (-(q * ((s + Δ : ℝ≥0) : ℝ))) -
        Real.exp (-(q * (s : ℝ)))) * V Z := by sorry
