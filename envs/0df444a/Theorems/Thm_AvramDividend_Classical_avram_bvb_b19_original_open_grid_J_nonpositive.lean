-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_original_open_grid_J_nonpositive
-- name    : AvramDividend.Classical.avram_bvb_b19_original_open_grid_J_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:50:52.905799+00:00
-- url     : https://prove2.me/theorems/d97ffc62-70d2-43f5-a3ec-c0da9a35111c
-- title:
--   Original BV open-cap finite-grid negative-mark J sum is nonpositive
-- statement:
--   For every original physical uniform-style nondecreasing time mesh, the negative-mark generator integral in each strictly interior pre-ruin sampled reserve cell is nonpositive by Proved phys88. Cell lengths and exponential discount are nonnegative, so the exact finite sum J_n is nonpositive, for any original X.ν and sample values Z. This is the complementary sign half to the proved closed-cap K_n sign, preserving boundary exclusion without assuming point-sampled contact occupation is measured.
-- source:
--   Original phys95 signed grid term J_n: each term is nonpositive by Proved phys88 with positive grid width and discount. Complement to BVB19 source-exact K_n sign beaa3373; convergence K_n-J_n remains separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys88_original_closed_cap_negative_mark_value_increment_nonpos
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b19_original_open_grid_J_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (Z : ℕ → ℝ) (σ : ℝ≥0∞) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < σ ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        (∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by sorry
