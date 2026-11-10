-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_discounted_cap_gaussian_mesh_bound
-- name    : AvramDividend.Classical.avram_gfinite15_original_discounted_cap_gaussian_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:06:00.268209+00:00
-- url     : https://prove2.me/theorems/89126069-557c-4e6f-aacb-45c489f2fca8
-- title:
--   Original finite Gaussian mesh has discounted quadratic cap-contact upper remainder
-- statement:
--   For every finite family of actual original-X/D clipped physical cells whose prepayment book reserve and frozen-dividend next reserve stay above a positive lower floor, the sum of discounted cap-linear Taylor increments is bounded by the exact original squared source increments weighted by the Gaussian discount. The cap crossing and cap-contact case are included without requiring a derivative at the cap. This is the source-specific finite-grid quadratic half of the stopped Gaussian Itô ledger and does not assert a stochastic expectation budget or endpoint limit.
-- source:
--   Root-connected 642de490 finite-cap original Gaussian source; applies public Proved 4745a3db global cap quadratic glue cellwise to the actual X.X and rightLimit D frozen cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_cap_quadratic_glue

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gfinite15_original_discounted_cap_gaussian_mesh_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (u c L : ℝ) (huC : u < c) (hL : 0 ≤ L)
    (hgrad : ∀ z ∈ Ico u c, 1 ≤ deriv w z)
    (hquad : ∀ z ∈ Ico u c, ∀ y ∈ Icc u c,
      w y ≤ w z + deriv w z * (y - z) + L / 2 * (y - z) ^ 2)
    (hgrowth : ∀ y ∈ Icc u c, c - y ≤ w c - w y)
    (q : ℝ) (ω : Ω) (S : Finset ℕ)
    (s t : ℕ → ℝ≥0)
    (hfloor : ∀ i ∈ S,
      u ≤ x + X.X (s i) ω - rightLimit D (s i) ω ∧
      u ≤ x + X.X (t i) ω - rightLimit D (s i) ω) :
    let V : ℝ → ℝ := fun y =>
      if y ≤ c then w y else w c + (y - c)
    let g : ℝ → ℝ := fun y => if y < c then deriv w y else 1
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (t i) ω - rightLimit D (s i) ω
    (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) *
      (V (Z i) - V (Y i) - g (Y i) * (Z i - Y i))) ≤
      L / 2 * (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) * (Z i - Y i) ^ 2) := by sorry
