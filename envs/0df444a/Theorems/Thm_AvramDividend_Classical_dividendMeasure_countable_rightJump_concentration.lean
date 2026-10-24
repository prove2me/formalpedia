-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_countable_rightJump_concentration
-- name    : AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-21T08:48:39.302927+00:00
-- url     : https://prove2.me/theorems/6e98697d-4ac5-42be-ba2c-d798755519a1
-- title:
--   The Lebesgue-Stieltjes measure of a dividend strategy is carried by the countable set of its right jumps
-- statement:
--   Let D be an adapted dividend strategy and let omega be a state. The Lebesgue-Stieltjes measure of the path of D at omega is carried by the set of times at which D has a right jump, that is the set of times t for which the right limit of D at t differs from D at t. The right-jump support of a monotone function is countable, so the dividend measure is concentrated on a countable set, and integrating against it is the same as integrating over that countable set. This is what allows a countable budget for the discounted dividends to bound the dividend measure of an arbitrary dividend strategy, whose payment times fill an interval and are therefore not themselves countable.
-- source:
--   The concentration of the Lebesgue-Stieltjes measure of a monotone function on its right-jump support, the countability of that support being the Proved theorem dividendStrategy_rightJump_support_countable and the atom mass being the Proved theorem dividendMeasure_singleton_eq_rightLimit_sub. This is the measure-theoretic ingredient that turns a countable budget for the discounted dividends into a bound for the dividend measure of an arbitrary dividend strategy. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (S : Set ℝ)
    (hS : S = {t : ℝ | 0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω}) :
    (dividendMeasure D ω).restrict S = dividendMeasure D ω := by sorry
