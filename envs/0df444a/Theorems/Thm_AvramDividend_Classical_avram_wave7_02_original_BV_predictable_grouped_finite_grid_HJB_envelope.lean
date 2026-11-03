-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_grouped_finite_grid_HJB_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_predictable_grouped_finite_grid_HJB_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:20:02.211278+00:00
-- url     : https://prove2.me/theorems/75c95cbd-5982-44ff-808d-63b655cb9da5
-- title:
--   Correctly grouped original BV predictable finite-grid discounted generator and dividend HJB envelope
-- statement:
--   On the actual original X, D and controlled predictable reserve left-limit, each nonnegative-weight discounted physical HJB generator and dividend derivative residual is nonpositive. Summing the parenthesised pair of summands together at each index over any finite grid gives a valid joint signed nonpositive bound. Unlike superseded 438c9c66, both weighted terms are inside the Finset sum binder.
-- source:
--   Fixes binder scope of superseded publication 438c9c66 (proof CE 22234), uses Proved original predictable source HJB a0879a2f and Finset.sum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_predictable_grouped_finite_grid_HJB_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : Finset ℝ≥0) (a b : ℝ≥0 → ℝ)
    (ha : ∀ t ∈ u, 0 ≤ a t)
    (hb : ∀ t ∈ u, 0 ≤ b t)
    (hregion : ∀ t ∈ u,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (∑ t ∈ u, (
      a t * (Real.exp (-(q * (t : ℝ))) *
        (X.drift * deriv w (Y t) +
          (∫ z in Iio (0 : ℝ),
            w (Y t + z) - w (Y t) ∂X.ν) - q * w (Y t))) +
      b t * (Real.exp (-(q * (t : ℝ))) *
        (1 - deriv w (Y t))))) ≤ 0 := by sorry
