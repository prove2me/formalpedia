-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:39:30.788719+00:00
-- url     : https://prove2.me/theorems/b55dacd6-6dc4-4fb2-9e43-07eb5fa2bfb6
-- title:
--   Original physical compact-interior discounted HJB drift plus nonnegative dividend-rate control inequality
-- statement:
--   For the actual original controlled Lévy X and dividend strategy D, at every compact-interior clipped reserve and arbitrary nonnegative continuous dividend outflow rate r, the sum of generator HJB drift and rate-times-derivative deficit is nonpositive after discounting. This is the drift/control sign required by an original-process stopped Ito-Meyer decomposition.
-- source:
--   Compose independently Proved same-source discounted HJB generator sign and discounted slope defect; multiplication by nonnegative physical dividend rate and ring identity preserve nonpositivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_hjb_discounted_generator_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_clipped_discounted_slope_defect_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_clipped_HJB_with_nonnegative_dividend_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (r : ℝ≥0 × Ω → ℝ) (hr : ∀ p, 0 ≤ r p) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    ∀ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        ((X.generator w (U p) - q * w (U p)) +
          r p * (1 - deriv w (U p))) ≤ 0 := by sorry
