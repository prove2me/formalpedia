-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_nat_horizon_bounds
-- name    : AvramDividend.Classical.dividendValue_le_of_nat_horizon_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:26:07.975437+00:00
-- url     : https://prove2.me/theorems/1a2e7cf5-7e35-4067-ae62-20b8c49d102f
-- title:
--   Monotone-convergence bridge from integer-horizon dividend bounds to full value
-- statement:
--   If the expected discounted dividends accumulated before ruin and before every deterministic integer horizon are uniformly bounded by B, then the full expected discounted dividend value is bounded by B. This is the monotone-convergence step after equation (5.13).
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, passage after equation (5.13) by monotone convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_nat_horizon_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by sorry
