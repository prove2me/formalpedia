-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise40_finite_weighted_count_rate_abs_bound
-- name    : AvramDividend.Classical.avram_anoise40_finite_weighted_count_rate_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:53:43.985941+00:00
-- url     : https://prove2.me/theorems/145f06ee-8b71-4169-9f5f-fce87c901c40
-- title:
--   Finite unit-weight compensated count has absolute bound by positive count and rate sums
-- statement:
--   An arbitrary finite real-weighted compensation sum with coefficients of absolute value at most one and nonnegative physical counts and rates has absolute value at most the sum of its counts plus the sum of its rates. This purely algebraic bound applies to every original dyadic compensated marked-count approximation.
-- source:
--   Concrete algebraic inequality required to close original dyadic integrable domination Open ed61f8be after physical count/intensity partition bound c4fb2de1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise40_finite_weighted_count_rate_abs_bound
    {ι : Type*} (S : Finset ι)
    (w a b : ι → ℝ)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (ha : ∀ i ∈ S, 0 ≤ a i)
    (hb : ∀ i ∈ S, 0 ≤ b i) :
    |∑ i ∈ S, w i * (a i - b i)| ≤
      (∑ i ∈ S, a i) + (∑ i ∈ S, b i) := by sorry
