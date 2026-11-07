-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route6_bv_original_physical_grid_full_signed_hjb_sum_nonpos
-- name    : AvramDividend.Classical.avram_route6_bv_original_physical_grid_full_signed_hjb_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:15:54.150252+00:00
-- url     : https://prove2.me/theorems/c4fc3aa2-60f6-4f4e-ae3b-606d2f5009e9
-- title:
--   Original BV physical-grid full generator plus dividend-gradient HJB source sum is nonpositive
-- statement:
--   On the actual bounded-variation X,D physical reserve grid at interior active reserve points, the entire discounted finite-cell sum of generator HJB terms and gradient-dividend terms is nonpositive. This is the original process HJB sign component of a stopped finite-grid source certificate; it assumes the true selected cells and genuine nonnegative D increments and does not assert martingale compensation or ruin/horizon atom cancellation.
-- source:
--   Physical-grid HJB signed source term of original stopped BV strategy, intended for c1e2f021, b39f2dd1 and 1a1a0301 after compensation, time-zero and ruin/horizon cell accounting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route6_bv_original_physical_grid_full_signed_hjb_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (cells : Finset ℕ)
    (hregion : ∀ i ∈ cells,
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C)
    (hdiv : ∀ i ∈ cells, D (u i) ω ≤ D (u (i + 1)) ω) :
    (∑ i ∈ cells,
      Real.exp (-(q * (u i : ℝ))) *
        (((u (i + 1) : ℝ) - (u i : ℝ)) *
          (X.generator w (riskProcess X x D (u i) ω) -
            q * w (riskProcess X x D (u i) ω)) +
        (D (u (i + 1)) ω - D (u i) ω) *
          (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by sorry
