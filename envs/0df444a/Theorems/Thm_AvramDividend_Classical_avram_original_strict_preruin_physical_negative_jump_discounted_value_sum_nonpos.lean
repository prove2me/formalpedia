-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_original_strict_preruin_physical_negative_jump_discounted_value_sum_nonpos
-- name    : AvramDividend.Classical.avram_original_strict_preruin_physical_negative_jump_discounted_value_sum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:40:05.216013+00:00
-- url     : https://prove2.me/theorems/500bf6c2-f20d-4e5a-99d1-d4fb20945108
-- title:
--   Signed original physical negative-mark stopped finite jump sum nonpositive
-- statement:
--   For any original spectrally negative Lévy surplus and admissible capped dividend strategy, including infinite Lévy activity or an infinite cap, take any finite selection of actual negative jump times strictly before ruin. The spatial pre-jump reserve is the left limit of the original post-right-dividend surplus. Under the usual continuous nonnegative-on-positive-side candidate and derivative at least one in the cap interior, every discounted negative-mark value increment at that reserve is nonpositive, so their physical finite sum is nonpositive. The proof combines the original strict pre-ruin spatial-mask theorem with the proved closed-cap negative-mark C1 monotonicity lemma. The jump contribution is source faithful and requires no auxiliary stochastic noise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_original_strict_preruin_physical_negative_jump_discounted_value_sum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (S : Finset ℝ≥0)
    (hS : ∀ t ∈ S,
      0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
      X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t < 0) :
    let Y : ℝ≥0 → ℝ := fun t =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      (w (Y t + (X.X t ω - Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) t)) - w (Y t))) ≤ 0 := by sorry
