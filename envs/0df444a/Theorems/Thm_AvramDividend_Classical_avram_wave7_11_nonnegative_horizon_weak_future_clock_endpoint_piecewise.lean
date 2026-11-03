-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_nonnegative_horizon_weak_future_clock_endpoint_piecewise
-- name    : AvramDividend.Classical.avram_wave7_11_nonnegative_horizon_weak_future_clock_endpoint_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:15:38.916476+00:00
-- url     : https://prove2.me/theorems/1fa61c36-5eb6-4dc8-a638-70712e18f61c
-- title:
--   Sharp all-nonnegative-horizon source Stieltjes endpoint correction for weakly future clock
-- statement:
--   For any original source dividendMeasure and stopped paymentTimes, and every nonnegative real finite horizon T, truncation by a weakly future clock η≥ENNReal.ofReal T changes the exact discounted Stieltjes reward only by a positive-horizon terminal singleton when η is exactly T. At T=0 the full initial dividend atom is already present in the truncated clock and no correction is needed. The theorem is pathwise and imposes no spurious atomlessness or extra positivity on the auxiliary clock.
-- source:
--   Proved zero-horizon original Stieltjes atom identity 1fb597ac and newly Proved weakly future positive-horizon endpoint correction 3dfaf6e8 (after publication).

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_nonnegative_horizon_weak_future_clock_endpoint_piecewise
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ η : ℝ≥0∞) (q T : ℝ)
    (hT : 0 ≤ T) (hFuture : ENNReal.ofReal T ≤ η) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (min σ η) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (if T = 0 then 0 else if η = ENNReal.ofReal T then
      (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      else 0) := by sorry
