-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed11_original_physical_grid_hjb_sign
-- name    : AvramDividend.Classical.avram_ubv_mixed11_original_physical_grid_hjb_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:04:40.006849+00:00
-- url     : https://prove2.me/theorems/ab8de325-caa8-4468-a461-0bec329d52d6
-- title:
--   Unrestricted original UBV physical-grid generator and dividend-gradient HJB sign
-- statement:
--   For the actual spectrally negative Levy process with arbitrary variation, every original physical interior grid has nonpositive discounted generator and dividend-gradient contribution. The previously proved BV source sign uses no bounded-variation assumption in its proof, but its declaration cannot be imported for the mixed UBV branch. This exact generalisation uses the full generator including Gaussian and compensated negative jumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed11_original_physical_grid_hjb_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
          (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by
  sorry
