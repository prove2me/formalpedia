-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_countable_rightJump_concentration_of_purely_atomic_nonneg
-- name    : AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration_of_purely_atomic_nonneg
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-22T02:28:37.577677+00:00
-- url     : https://prove2.me/theorems/80fd3926-57be-4123-a997-3ebd7f065d4c
-- title:
--   The dividend measure is carried by the countable set of right jumps when it has no continuous part on the non-negative half-line
-- statement:
--   The countable right-jump concentration statement for the Lebesgue-Stieltjes measure of a dividend strategy, with the no-continuous-part hypothesis restricted to intervals of the non-negative half-line. The Lebesgue-Stieltjes measure of a monotone function need not be carried by its right jumps: the measure of an interval (a, b] is the increase of the function across the interval, which for a left-continuous monotone function decomposes into the sum of its right jumps in that interval plus a continuous part. The hypothesis that the measure of every interval (a, b] with 0 <= a <= b equals the increase of the right limit of the dividend path across that interval is exactly the statement that the dividend measure has no continuous part there, and under it the measure is carried by the countable set of right jumps. This is the form of the hypothesis that the unbounded-variation stochastic core admissible_cap_truncated_ubv_stochastic_core needs, because the set of right jumps of the dividend path lives entirely in the non-negative half-line. It refines the published theorem dividendMeasure_countable_rightJump_concentration_of_purely_atomic, whose hypothesis quantifies over all real endpoints: that version asks for the same statement on intervals that reach below the origin, where the right limit of the dividend path at the origin need not vanish for a general dividend strategy.
-- source:
--   The non-negative-range variant of the published theorem dividendMeasure_countable_rightJump_concentration_of_purely_atomic. The measure of an interval (a, b] for the dividend measure is the increase of the right limit of the dividend path, which decomposes into the sum of the right jumps of that path in the interval plus a continuous part; the hypothesis hatomic is the assumption that the continuous part vanishes. Together with the Proved countability of the right-jump set, dividendStrategy_countable_rightJump_times, this makes the dividend measure carried by a countable set, which is what allows a countable budget for the discounted dividends to bound the dividend measure of a dividend strategy. The restriction 0 <= a is what the unbounded-variation stochastic core needs, since the right-jump set of the dividend path is contained in the non-negative half-line, and it avoids asking for the statement on intervals that reach below the origin, where the right limit of the dividend path at the origin need not vanish for a general dividend strategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration_of_purely_atomic_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (S : Set ℝ)
    (hS : S = {t : ℝ | 0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω})
    (hatomic : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      dividendMeasure D ω (Ioc a b) =
        ENNReal.ofReal (rightLimit D b.toNNReal ω - rightLimit D a.toNNReal ω)) :
    (dividendMeasure D ω).restrict S = dividendMeasure D ω := by sorry
