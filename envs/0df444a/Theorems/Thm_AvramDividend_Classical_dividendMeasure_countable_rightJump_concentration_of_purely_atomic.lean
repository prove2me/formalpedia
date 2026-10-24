-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_countable_rightJump_concentration_of_purely_atomic
-- name    : AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration_of_purely_atomic
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-21T11:36:30.908208+00:00
-- url     : https://prove2.me/theorems/76715a90-91f3-4db6-ad64-9afae72f3329
-- title:
--   The Lebesgue-Stieltjes measure of a dividend strategy without a continuous part is carried by the countable set of its right jumps
-- statement:
--   The corrected form of the countable right-jump concentration statement for the Lebesgue-Stieltjes measure of a dividend strategy. The Lebesgue-Stieltjes measure of a monotone function need not be carried by its right jumps: the measure of an interval (a, b] is the increase of the function across the interval, which for a left-continuous monotone function decomposes into the sum of its right jumps in that interval plus a continuous part. The hypothesis that the measure of every interval (a, b] equals the increase of the right limit of the dividend path across that interval is exactly the statement that the dividend measure has no continuous part, and under it the measure is carried by the countable set of right jumps. The countability of that set is the Proved theorem dividendStrategy_countable_rightJump_times. This is the statement needed to turn a countable budget for the discounted dividends into a bound for the dividend measure of a dividend strategy whose payments fill an interval and are therefore not themselves countable.
-- source:
--   The corrected countable right-jump concentration statement for the Lebesgue-Stieltjes measure of a dividend strategy. The measure of an interval (a, b] for the dividend measure is the increase of the right limit of the dividend path, which decomposes into the sum of the right jumps of that path in the interval plus a continuous part; the hypothesis hatomic is the assumption that the continuous part vanishes. Together with the Proved countability of the right-jump set, dividendStrategy_countable_rightJump_times, this makes the dividend measure carried by a countable set, which is what allows a countable budget for the discounted dividends to bound the dividend measure of a dividend strategy. This supersedes the earlier statement dividendMeasure_countable_rightJump_concentration, which omitted the no-continuous-part hypothesis and is therefore false for a general dividend strategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration_of_purely_atomic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (S : Set ℝ)
    (hS : S = {t : ℝ | 0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω})
    (hatomic : ∀ a b : ℝ, a ≤ b →
      dividendMeasure D ω (Ioc a b) =
        ENNReal.ofReal (rightLimit D b.toNNReal ω - rightLimit D a.toNNReal ω)) :
    (dividendMeasure D ω).restrict S = dividendMeasure D ω := by sorry
