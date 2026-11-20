-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_stop_terminal_caplinear_nonnegative_with_contact
-- name    : AvramDividend.Classical.avram_f6_original_true_stop_terminal_caplinear_nonnegative_with_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:35:22.477244+00:00
-- url     : https://prove2.me/theorems/478646aa-6d8e-44ce-952f-00cbed8fa4fa
-- title:
--   True original stopped terminal caplinear positive at pre-ruin or nonpositive ruin contact
-- statement:
--   Original true-X pointwise terminal positivity at any stopped clock t that is zero, strictly before original ruin, or has a nonpositive ruin reserve at contact. On the pre-ruin branch use the actual postpayment x+X_t-rightLimit D_t and nonnegative caplinear value. At ruin use the original riskProcess branch, w(0)>=0, and negative w=0, so Gaussian creeping and negative-jump overshoot are both included. Multiply the physically correct value by exp(-q t). No stochastic witness is invented.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_stop_terminal_caplinear_nonnegative_with_contact
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
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (hCase : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω ∨
      riskProcess X x D t ω ≤ 0) :
    let Y : ℝ := if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    0 ≤ Real.exp (-(q * (t : ℝ))) *
      (if ENNReal.ofReal Y ≤ C then w Y
       else w C.toReal + (Y - C.toReal)) := by sorry
