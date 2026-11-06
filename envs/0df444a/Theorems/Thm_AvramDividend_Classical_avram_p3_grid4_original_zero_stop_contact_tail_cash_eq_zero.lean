-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_zero_stop_contact_tail_cash_eq_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_original_zero_stop_contact_tail_cash_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:02:55.442917+00:00
-- url     : https://prove2.me/theorems/7aefc735-f745-46ca-bf7e-3b35e2f24a41
-- title:
--   Original strictly positive contact tail is empty at zero stopped ruin/horizon clock
-- statement:
--   For the actual original X/D ruin/horizon-clamped clock equal to zero, the literal original paymentTimes-discounted dividendMeasure contact-tail interval Ioc(max(tau-T/(m+1),0),tau) is empty and its ENNReal cash mass is zero. The initial dividend rightLimit D 0 atom is accounted in the separate full-stop budget, not incorrectly suppressed by this strictly positive Ioc tail statement.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_zero_stop_contact_tail_cash_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (T : ℝ≥0)
    (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    τ = 0 →
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by sorry
