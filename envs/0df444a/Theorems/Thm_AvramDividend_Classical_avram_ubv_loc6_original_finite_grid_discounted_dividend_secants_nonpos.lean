-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_finite_grid_discounted_dividend_secants_nonpos
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_finite_grid_discounted_dividend_secants_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:27:55.816729+00:00
-- url     : https://prove2.me/theorems/f9a26434-489a-4dfb-9647-5b3b0e98c02c
-- title:
--   Original stopped physical dividend secant residual is nonpositive on every finite discounted payment grid
-- statement:
--   For any finite original physical payment-time grid with each time equal to zero or strictly before ruin, summing the discounted real excess of a dividend jump over its exact w-value secant produces a nonpositive total. The time-zero right dividend is included, and a positive-time ruin jump is excluded in the original paymentTimes convention.
-- source:
--   Exact original jump secant hypothesis from the canonical UBV localisation certificate, applied at each physical payment tag with the positive discount factor exp(-q t) and summed over the finite grid. No side conditions beyond the original time-zero/pre-ruin condition are introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_original_finite_grid_discounted_dividend_secants_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hS : ∀ t ∈ S, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))))) ≤ 0 := by sorry
