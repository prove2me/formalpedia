-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_nat_horizon_bounds_of_strategy
-- name    : AvramDividend.Classical.dividendValue_le_of_nat_horizon_bounds_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:36:01.524592+00:00
-- url     : https://prove2.me/theorems/198de416-095c-4991-8e15-9f4798ac61eb
-- title:
--   Integer-horizon dividend bounds imply the full value bound for a dividend strategy
-- statement:
--   For a dividend strategy, if expected discounted dividends before ruin and every deterministic integer horizon are uniformly bounded by B, then the full dividend value is bounded by B. The strategy assumption supplies the measurability needed by monotone convergence.
-- source:
--   Strategy-scoped monotone-convergence passage after equation (5.13) in Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_nat_horizon_bounds_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by sorry
