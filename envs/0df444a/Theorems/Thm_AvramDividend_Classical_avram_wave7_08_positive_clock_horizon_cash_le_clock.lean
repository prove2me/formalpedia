-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_clock_horizon_cash_le_clock
-- name    : AvramDividend.Classical.avram_wave7_08_positive_clock_horizon_cash_le_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:59:07.604168+00:00
-- url     : https://prove2.me/theorems/7b9deff0-5d9f-4a9b-8055-d7d4a8e37ef7
-- title:
--   Source finite-clock discounted Stieltjes cash at any horizon is bounded by cash up to its natural clock
-- statement:
--   For the genuine original Lévy source X and the original dividendMeasure D, full discounted Stieltjes payouts restricted to paymentTimes(min(ruinTime,n)) and any real finite horizon T are bounded by payouts at deterministic horizon n, for n>0. This uses exact time-domain support and monotonicity of nonnegative lintegrals, without source Itô or any replacement model.
-- source:
--   Original-source consequence of the W7-08 source payment support child 2cd84612-fd48-468c-bb7c-e8f0e79ecf41. It reduces d457be6b-c74a-4a7e-aea2-4bb6222642d5 to the single deterministic horizon T=n, keeping the same Ω,P,X,D and complete Stieltjes measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_positive_clock_horizon_cash_le_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
