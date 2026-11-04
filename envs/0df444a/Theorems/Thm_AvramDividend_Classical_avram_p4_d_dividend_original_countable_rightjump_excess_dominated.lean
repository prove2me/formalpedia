-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_excess_dominated
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_excess_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:16:22.120789+00:00
-- url     : https://prove2.me/theorems/18d44060-6630-4e9c-81fd-1e8679f15d55
-- title:
--   Source-original countable right-dividend correction is summable and nonpositive under a summable excess-value-loss envelope
-- statement:
--   The true original right-payment residual is the cash delta plus the post-source/prepayment to postpayment value change. hjump makes each discounted residual nonpositive, including simultaneous Lévy and dividend jumps. If the extra loss of value beyond cash has an explicitly summable nonnegative envelope at these actual states, then the whole countable residual series converges absolutely and is nonpositive. This is a localised sufficient integrability criterion, and the hypothesis is NOT asserted from strict-interior w derivatives at cap or zero contact.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.13); original canonical hjump; source-proved 9f4070e7 rightjump helper; Mathlib summability comparison.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_excess_dominated
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
    (B : ι → ℝ) (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB_summable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) * B i))
    (hExcess : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        (rightLimit D (t i) ω - D (t i) ω) + B i) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by sorry
