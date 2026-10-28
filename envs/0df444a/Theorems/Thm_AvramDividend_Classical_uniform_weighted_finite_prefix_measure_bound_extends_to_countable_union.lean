-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
-- name    : AvramDividend.Classical.uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:42:45.097093+00:00
-- url     : https://prove2.me/theorems/867ff1ee-fbec-4625-adb6-6735002b6f65
-- title:
--   Uniform weighted probability bounds for increasing finite-prefix events extend to the infinite union
-- statement:
--   Let s_n be an increasing sequence of measurable events and μ any measure, and let a be any nonnegative extended-real weight. If for every n, a·μ(s_n)≤1, then the same estimate holds for the countable union s_∞=⋃_n s_n. This converts the finite-horizon Esscher Doob sampled-downcrossing bound, uniformly in the number of grid points, into the countable-grid lower-ruin crossing bound under a fixed terminal law.
-- source:
--   Use pinned Mathlib `Monotone.measure_iUnion` to express the measure of the increasing measurable union as the supremum of finite measures. Multiply and commute the nonnegative extended-real multiplication through iSup with pinned `ENNReal.mul_iSup`; conclude using `iSup_le` and the hypothesis for each finite prefix. This generic measure-continuity lemma does not require that μ be finite.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Inv
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (s : ℕ → Set Ω)
    (hs : Monotone s) (hms : ∀ n : ℕ, MeasurableSet (s n))
    (a : ℝ≥0∞)
    (hfinite : ∀ n : ℕ, a * μ (s n) ≤ 1) :
    a * μ (⋃ n, s n) ≤ 1 := by sorry
