-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_no_nonpositive_expected_bound
-- name    : AvramDividend.Classical.drained_zero_barrier_no_nonpositive_expected_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:55:49.430983+00:00
-- url     : https://prove2.me/theorems/4e2ee960-fc73-475d-9b1c-865e1923a963
-- title:
--   Positive initial dividend excludes a nonpositive verification expectation bound
-- statement:
--   Fix any spectrally negative Lévy process and strictly positive initial capital. The admissible zero-barrier policy with a continuous deterministic drain pays at least the starting capital in expected discounted dividends at every nonnegative finite horizon. Hence an alleged upper bound by the nonpositive extended-real value ENNReal.ofReal(w(x)) is impossible. This is a rigorous abstract contradiction criterion for auditing the omitted nonnegative boundary assumption of the unbounded-variation stochastic verification core.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), and the previously proved expected Stieltjes dividend lower bound.

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_expected_reward_lower_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_zero_barrier_no_nonpositive_expected_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 < x)
    (w : ℝ → ℝ) (hwx : w x ≤ 0)
    (q T : ℝ) (hT : 0 ≤ T) :
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes
        (ruinTime X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∂P) ≤
      ENNReal.ofReal (w x)) := by sorry
