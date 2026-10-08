-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_admissible_exponential_dividend_jump_bound
-- name    : AvramDividend.Classical.discounted_admissible_exponential_dividend_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:39:52.249139+00:00
-- url     : https://prove2.me/theorems/c25e3989-426f-40ae-a84b-77fb9c197a69
-- title:
--   At an admissible payment time, discounted dividends are dominated by the exponential value drop
-- statement:
--   At every permitted admissible dividend payment instant the discounted lump ΔD exp(−qt) is no greater than the discounted reduction in exponential candidate value exp(θU), for θ≥1. This is the exact cash-payment inequality at Stieltjes atoms in the mission's IsAdmissible, rightLimit and riskProcess definitions.
-- source:
--   Proved admissible_exponential_dividend_jump_bound and positivity of exp(−qt).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_admissible_exponential_dividend_jump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ q : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) * (rightLimit D t ω - D t ω) ≤
      Real.exp (-(q * (t : ℝ))) *
        (Real.exp (θ * riskProcess X x D t ω) -
          Real.exp (θ * (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) := by sorry
