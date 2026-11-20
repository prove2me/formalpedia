-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_preruin_discounted_caplinear_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_preruin_discounted_caplinear_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:33:24.804528+00:00
-- url     : https://prove2.me/theorems/f1eef789-170a-404c-9986-2815c0c74305
-- title:
--   True original pre-ruin discounted caplinear terminal nonnegative at all bounded clocks
-- statement:
--   On the original same-X risk process, at any genuine time t=0 or t strictly before ruin, the postpayment reserve x+X_t-rightLimit D_t is nonnegative by published original admissibility. Consequently the canonical caplinear extension of original w is nonnegative and its actual discounted terminal reward remains nonnegative, including above the finite cap after Gaussian fluctuations. No random martingale witness, no hypothesis on w beyond the cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_preruin_discounted_caplinear_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ Real.exp (-(q * (t : ℝ))) *
      (let y := x + X.X t ω - rightLimit D t ω
       if ENNReal.ofReal y ≤ C then w y
       else w C.toReal + (y - C.toReal)) := by sorry
