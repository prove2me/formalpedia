-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_terminal_cash_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_top9_original_topcap_terminal_cash_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:02:26.543565+00:00
-- url     : https://prove2.me/theorems/108a0c60-40c8-4545-b4e4-2accbe9f9cd9
-- title:
--   Original infinite-cap terminal plus closed-clock cash is nonnegative
-- statement:
--   For the actual terminal post-payment reserve at the ruin or integer horizon clock, and actual closed-Iic discounted dividend cash, the terminal-plus-cash payoff is pointwise nonnegative under the source infinite-cap HJB gradient and cemetery assumptions.
-- source:
--   Uses accepted topcap global value nonnegativity 5224d9f0, exact original Term and Cash definitions from canonical 148b2516, and ENNReal.toReal_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_topcap_terminal_cash_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (W Cash Term : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, 0 ≤ Term ω + Cash ω := by sorry
