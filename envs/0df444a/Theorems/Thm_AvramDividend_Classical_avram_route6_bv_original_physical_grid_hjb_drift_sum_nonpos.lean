-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route6_bv_original_physical_grid_hjb_drift_sum_nonpos
-- name    : AvramDividend.Classical.avram_route6_bv_original_physical_grid_hjb_drift_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:13:55.332427+00:00
-- url     : https://prove2.me/theorems/a9da23bc-6b8c-4621-9d17-41bd12ee1db4
-- title:
--   Original bounded-variation physical grid discounted generator-HJB drift sum is nonpositive on active cells
-- statement:
--   For actual stopped bounded-variation riskProcess reserves at physical grid nodes strictly inside the positive cap, the discounted finite-cell HJB drift contribution is nonpositive. The proof uses each true generator inequality, positivity of exponential discount, and nonnegative physical clock increments. This isolates the sign obligation for the original source reconciliation without assuming away ruin or right-payment atoms.
-- source:
--   Avram original BV HJB physical-clock drift sign, a finite-cell input to c1e2f021 and b39f2dd1 source certificates; does not claim terminal, compensated martingale or dividend accounting.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route6_bv_original_physical_grid_hjb_drift_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (cells : Finset ℕ)
    (hregion : ∀ i ∈ cells,
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    (∑ i ∈ cells,
      Real.exp (-(q * (u i : ℝ))) *
        ((u (i + 1) : ℝ) - (u i : ℝ)) *
          (X.generator w (riskProcess X x D (u i) ω) -
            q * w (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
