-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_truncated_zero_reward_eq_initial_capital
-- name    : AvramDividend.Classical.drained_zero_barrier_truncated_zero_reward_eq_initial_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:24:41.184036+00:00
-- url     : https://prove2.me/theorems/2fe36451-5142-4c2a-928c-b1a956d4f3a6
-- title:
--   Drained zero-barrier control retains the exact initial Stieltjes dividend reward
-- statement:
--   The deterministic linear dividend drain produces no additional payment atom at the initial time, so the zero-horizon discounted Stieltjes reward of the drained zero-barrier strategy remains exactly the initial nonnegative capital x. This holds for every sample path, discount rate and extended ruin horizon, including the zero-ruin-time case. It is the time-zero reward identity needed for the unbounded-variation verification counterexample.
-- source:
--   Avram, Palmowski and Pistorius (2007), initial barrier dividend definition and Proposition 4(i) boundary, combined with the Proved zero-horizon Stieltjes reward and barrier jump identities.

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain_initial_rightLimit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_zero_barrier_truncated_zero_reward_eq_initial_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (q : ℝ) (σ : ℝ≥0∞) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω)) =
      ENNReal.ofReal x := by sorry
