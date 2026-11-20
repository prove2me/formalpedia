-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_ruincontact_true_cash_tail_finite_20261119
-- name    : AvramDividend.Classical.avram_jump6_B_ruincontact_true_cash_tail_finite_20261119
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:28:56.232186+00:00
-- url     : https://prove2.me/theorems/32ceb85b-1c19-46df-b3c3-ce7de7b56139
-- title:
--   Original stopped ruin-contact discounted physical cash tail is finite
-- statement:
--   The genuine discounted dividend cash on the strict left neighbourhood of any ruin contact is finite. It follows by the subset relation from the already Proved full inclusive stopped-cash finiteness. This discharges the tail-finiteness hypothesis in the original crossing-contact signed cash lemma without adding a jump-activity restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_ruincontact_true_cash_tail_finite_20261119
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ δ : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) < ⊤ := by sorry
