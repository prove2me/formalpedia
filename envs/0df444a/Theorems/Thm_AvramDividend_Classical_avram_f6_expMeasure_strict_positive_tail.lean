-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_expMeasure_strict_positive_tail
-- name    : AvramDividend.Classical.avram_f6_expMeasure_strict_positive_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:16:12.179184+00:00
-- url     : https://prove2.me/theorems/131d3a7a-dd21-4176-9c19-d0f69300af85
-- title:
--   True exponential random clock has positive mass beyond every finite nonnegative horizon
-- statement:
--   For a genuine exponential measure expMeasure(p) with p>0, every n≥0 has positive tail mass (expMeasure p)(Ioi n)>0. Use exact exponential CDF, probability normalization and complement to prove. Needed to restrict an existing Proved exponential-clock supremum bound to deterministic horizon.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_expMeasure_strict_positive_tail (p n : ℝ) (hp : 0 < p) (hn : 0 ≤ n) :
    0 < expMeasure p (Ioi n) := by sorry
