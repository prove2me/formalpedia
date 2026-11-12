-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger86_original_terminal_payment_cancel
-- name    : AvramDividend.Classical.avram_gledger86_original_terminal_payment_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:47:00.143271+00:00
-- url     : https://prove2.me/theorems/5e267f9e-63bd-4ef7-9524-61e06dbcf0d1
-- title:
--   Terminal original prepayment reward cancels the crossing-cell postpayment reward
-- statement:
--   The terminal postpayment and prepayment reward corrections at the original stopped clock combine to a nonpositive discounted contribution whenever the original dividend right limit at a previous cell start is no greater than the actual dividend at the clock. The global top-cap reward is monotone even across zero.
-- source:
--   Genuine terminal crossing-cell cancellation obligation of gledger81 16e988d7, separate from gledger83 positive-prefix cash and gledger84 final-strip cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger86_original_terminal_payment_cancel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (ρ a : ℝ≥0)
    (hDiv : rightLimit D a ω ≤ D ρ ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
        (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) ≤ 0 := by sorry
