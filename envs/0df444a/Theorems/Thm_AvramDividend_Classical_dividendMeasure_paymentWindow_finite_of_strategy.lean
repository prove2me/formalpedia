-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
-- name    : AvramDividend.Classical.dividendMeasure_paymentWindow_finite_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:05:38.181778+00:00
-- url     : https://prove2.me/theorems/6f41c374-04ef-44c0-a9dd-1663f1cf8195
-- title:
--   Every stopped finite-horizon dividend payment window has finite Stieltjes mass
-- statement:
--   For a dividend strategy D, a path ω, any ruin bound σ and nonnegative horizon T, the Stieltjes measure of paymentTimes σ intersected with (-∞,T] is finite. The payment window is contained in [0,T+1); the previously verified measure identity says the mass of that enclosing interval equals the finite quantity ENNReal.ofReal (D (T+1) ω). This removes an explicit finiteness hypothesis from discounted payout integral conversion.

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Mathlib.Tactic.NormNum

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendMeasure_paymentWindow_finite_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0) :
    dividendMeasure D ω (paymentTimes σ ∩ Iic (T : ℝ)) ≠ ⊤ := by sorry
