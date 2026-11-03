-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_nonnegative_horizon_expected_exact_endpoint_piecewise
-- name    : AvramDividend.Classical.avram_wave7_11_nonnegative_horizon_expected_exact_endpoint_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:18:09.329979+00:00
-- url     : https://prove2.me/theorems/db3112f0-ada4-4f55-9eab-f1dc6208d89d
-- title:
--   Exact all-nonnegative finite horizon expected Stieltjes payment identity with correct time-zero atom
-- statement:
--   For every real T≥0 in the exact original Lévy dividend problem, complete expected Stieltjes payout through ruin is strict min(ruinTime,T) payout plus the original T singleton contribution if T>0, with no extra contribution when T=0 because the clock convention already includes the original time-zero right-limit atom. This piecewise identity distinguishes the structurally different endpoint cases and prevents double-counting of the initial atom.
-- source:
--   Proved W7-11 zero-horizon full original Stieltjes atom theorem, W7-11 positive-horizon exact original expected endpoint decomposition, original source X/P/D.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_nonnegative_horizon_expected_exact_endpoint_piecewise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (if T = 0 then 0 else
      (∫⁻ ω, ∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)) := by sorry
