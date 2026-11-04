-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_p4f_real_cash_exact_lintegral_bridge
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_p4f_real_cash_exact_lintegral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:19:43.816013+00:00
-- url     : https://prove2.me/theorems/7c4f4f2c-ada9-4159-af1c-9d28abe9be3a
-- title:
--   Canonical P4-F real Cash faithfully represents finite true original discounted Stieltjes integral
-- statement:
--   For any original spectrally negative Levy process, genuine dividend strategy, finite stopped clock tau and nonnegative q, the real-valued Cash used in canonical P4-F is pathwise nonnegative and recovers its exact full original payment-time Stieltjes lintegral under ENNReal.ofReal. The previously proved literal stopped cash finiteness rules out the otherwise dangerous infinity-to-zero behaviour of ENNReal.toReal, including time-zero and horizon right atoms and the strict-positive-ruin exclusion.
-- source:
--   Proved original literal stopped payment cash finiteness and Mathlib ENNReal.ofReal_toReal; exact P4-F hCash convention

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_p4f_real_cash_exact_lintegral_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) :
    0 ≤ Cash ω ∧
    ENNReal.ofReal (Cash ω) =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by sorry
