-- Prove2me | Theorems.Thm_AvramDividend_Classical_truncated_dividend_path_value_aemeasurable
-- name    : AvramDividend.Classical.truncated_dividend_path_value_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:14:54.666224+00:00
-- url     : https://prove2.me/theorems/6910ce78-fe88-4e1c-b7f1-e02141ed6b74
-- title:
--   Finite-horizon Stieltjes dividend value is measurable in the sample point
-- statement:
--   For an admissible dividend strategy and a fixed deterministic integer horizon, the pathwise discounted Stieltjes dividend integral up to ruin and that horizon is almost-everywhere measurable as a function of the sample point. This is exactly the sample-space measurability needed to apply monotone convergence to the outer expectation.
-- source:
--   Measure-theoretic regularity implicit in the monotone-convergence step of Avram-Palmowski-Pistorius Proposition 4(i), based on adapted left-continuous monotone dividend paths and the ruin-time construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.truncated_dividend_path_value_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) (n : ℕ) :
    AEMeasurable
      (fun ω => ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) P := by sorry
