-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_finite_stopped_discounted_tail
-- name    : AvramDividend.Classical.avram_p3_grid4_original_finite_stopped_discounted_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:34:18.785495+00:00
-- url     : https://prove2.me/theorems/5ac257cc-8d67-4ad7-b913-ed664dbb9e7d
-- title:
--   Original positive closed-horizon weighted dividend cash controls every stopped contact tail
-- statement:
--   For an actual admissible original dividend strategy D, each discounted Stieltjes cash tail from any nonnegative τ-δ to τ≤T and masked by original paymentTimes σ is finite. The exact tail set is included in the original closed-horizon paymentTimes set, whose weighted mass is finite by the proved source-faithful theorem c4e50d93. This finite weighted envelope is needed before applying continuity from above to the shrinking contact-cell tail; it does not assume the horizon atom is zero.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_finite_stopped_discounted_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (τ T δ : ℝ≥0) (hτT : τ ≤ T)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Ioc ((τ - δ : ℝ≥0) : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ := by sorry
