-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_expected_closed_horizon_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_expected_closed_horizon_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:25:45.907493+00:00
-- url     : https://prove2.me/theorems/847490c4-6adc-4d89-a7b9-07ec42e398e5
-- title:
--   Expected complete original BV closed-horizon dividend reward on all positive-ruin paths
-- statement:
--   The actual bounded-variation Lévy model admits a deterministic expectation bound for the entire original dividend Stieltjes reward through a closed time horizon T, including the terminal right atom and paths ruined before T, on the event that ruin is strictly positive. For any later H the expected reward is at most x plus H times the physical drift.
-- source:
--   The original positive-ruin closed-horizon pathwise Stieltjes bound and integration against the original probability law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_closed_horizon_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_expected_closed_horizon_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T H : ℝ≥0) (hTH : T < H) :
    (∫⁻ ω, if 0 < ruinTime X x D ω then
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) else 0 ∂P) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by sorry
