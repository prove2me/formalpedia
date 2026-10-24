-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_continuous_nonzero_not_rightJump_concentrated
-- name    : AvramDividend.Classical.dividendMeasure_continuous_nonzero_not_rightJump_concentrated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:38:03.419451+00:00
-- url     : https://prove2.me/theorems/8a6557bb-6fb0-4d59-b382-8fb6cea8e4af
-- title:
--   A nonzero continuous dividend Stieltjes measure cannot be concentrated on its right-jump set
-- statement:
--   Let D be a cumulative dividend process on a fixed sample path with no right jump at any nonnegative time. If its Stieltjes dividend measure assigns positive (nonzero) mass to some bounded real interval, then that measure cannot be recovered by restricting it to the set of right dividend jumps. Indeed the set of right jumps is empty by continuity, so the restriction is zero, contrary to the positive original mass. This establishes the exact formal obstruction to erroneous right-jump concentration lemmas that silently ignore continuous dividends, independently of whether the process has a Lévy martingale component.
-- source:
--   Pure measure-theoretic counter-obstruction to false AvramDividend.Classical.dividendMeasure_countable_rightJump_concentration; valid for every process and measurable space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_continuous_nonzero_not_rightJump_concentrated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (S : Set ℝ)
    (hS : S = {t : ℝ | 0 ≤ t ∧
      rightLimit D t.toNNReal ω ≠ D t.toNNReal ω})
    (hContinuous : ∀ t : ℝ≥0, rightLimit D t ω = D t ω)
    (a b : ℝ) (hPositive : dividendMeasure D ω (Ioc a b) ≠ 0) :
    (dividendMeasure D ω).restrict S ≠ dividendMeasure D ω := by sorry
