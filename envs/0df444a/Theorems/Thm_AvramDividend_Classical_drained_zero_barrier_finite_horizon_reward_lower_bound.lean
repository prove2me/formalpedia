-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_finite_horizon_reward_lower_bound
-- name    : AvramDividend.Classical.drained_zero_barrier_finite_horizon_reward_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:47:24.643526+00:00
-- url     : https://prove2.me/theorems/a0f9ad71-7eee-44c8-b3e2-ff481d72211d
-- title:
--   Instantly ruined dividend strategy pays at least initial capital on every finite horizon
-- statement:
--   The admissible zero-barrier dividend policy with continuous deterministic drain pays an initial Stieltjes atom of x. The payment at time zero contributes to every time horizon T≥0, even though the ruin time is zero; hence the discounted reward integral is at least x pathwise. This prevents omission of the initial dividend in the boundary-value verification argument.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), and the existing proven Stieltjes initial-atom identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_truncated_zero_reward_eq_initial_capital

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_zero_barrier_finite_horizon_reward_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (q T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    ENNReal.ofReal x ≤
      (∫⁻ t in paymentTimes
          (ruinTime X x
            (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω)) := by sorry
