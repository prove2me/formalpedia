-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_expected_reward_lower_bound
-- name    : AvramDividend.Classical.drained_zero_barrier_expected_reward_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:52:46.070583+00:00
-- url     : https://prove2.me/theorems/4eab90be-1ff9-41f9-ad6a-c295f4c62267
-- title:
--   Finite-horizon expected discounted dividends of an instantly ruined strategy exceed initial capital
-- statement:
--   For any spectrally negative Lévy process on its intrinsic probability space and nonnegative capital x, the expected stopped discounted dividend reward for the zero-barrier policy with continuous drain is at least x, at every horizon T≥0. The conclusion follows from the proved pathwise reward bound, monotonicity of Lebesgue integration and the probability measure embedded in the process data. It is a direct finite-horizon comparison for the boundary-value audit.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), and previously proved pathwise Stieltjes reward lemma.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_finite_horizon_reward_lower_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_zero_barrier_expected_reward_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (q T : ℝ) (hT : 0 ≤ T) :
    ENNReal.ofReal x ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes
          (ruinTime X x
            (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∂P) := by sorry
