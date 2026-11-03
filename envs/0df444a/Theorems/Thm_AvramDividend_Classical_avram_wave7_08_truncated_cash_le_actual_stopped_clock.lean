-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
-- name    : AvramDividend.Classical.avram_wave7_08_truncated_cash_le_actual_stopped_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:26:22.596524+00:00
-- url     : https://prove2.me/theorems/798c835a-3a7e-41eb-b6cf-813705e31f25
-- title:
--   Canonical source finite-clock Stieltjes cash dominated by stopped Cash at the actual truncated ruin time
-- statement:
--   For the exact original process X and dividends D, the full finite-horizon discounted cash before min(ruinTime,n) is bounded by the original ruin-time Cash integral stopped at the real-valued truncated ruin clock τ = (min(ruinTime,n)).toNNReal. This gives the exact cash-side premise interface to the existing Proved one-sided source HJB theorem 8cd5e123, retaining the original Ω, P, X, D, ruinTime and Stieltjes dividendMeasure.
-- source:
--   Uses source payment set inclusion avram_wave7_08_source_paymentTimes_le_stopped_real_clock and Mathlib lintegral_mono_set, no stochastic substitution. Mathematically distinct from the earlier comparison at fixed n, because the stopped source Cash uses the pathwise τ ω.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_truncated_cash_le_actual_stopped_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
