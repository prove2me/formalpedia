-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_signed_tsum_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_signed_tsum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:14:13.553714+00:00
-- url     : https://prove2.me/theorems/c36535cc-b95b-41b6-9bad-495860a5eb01
-- title:
--   Countable original post-source right-dividend residual sums are signed at every eligible payment time
-- statement:
--   For any indexed collection of source-original eligible right payment times (including initial and horizon times), the actual discounted finite-variation dividend right-jump secant residuals are termwise nonpositive by the canonical explicit hjump at the post-source, prepayment state. Under honest summability of the entire real signed series, its countable sum is nonpositive, including simultaneous Lévy source/payment jumps and arbitrarily many payment times. This is the right-atomic signed remainder and does not assert the missing Stieltjes countable representation or Itô–Meyer identity.
-- source:
--   Avram–Palmowski–Pistorius, Proposition 4(i), Eq. (5.13); original P4-F hjump and riskProcess, source-accepted P4-D rightjump lemma 9f4070e7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_signed_tsum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hSummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω)))) :
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by sorry
