-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger63_compact_continuous_value_finite_lower_bound
-- name    : AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:37:29.519362+00:00
-- url     : https://prove2.me/theorems/73379335-c038-4c00-afa5-bc27c0cb471b
-- title:
--   Continuity bounds the negative value tail on a compact strictly positive reserve band
-- statement:
--   The value of a continuous function on a fixed compact real interval is bounded below by a finite deterministic negative number. The original stopped Gaussian compact-prefix reserve lies in a fixed strictly positive band, so this bound controls the potentially large negative initial postpayment value in every active physical cell. It is combined with the Gaussian HJB one-sided exponential upper envelope in the source sum estimate.
-- source:
--   Necessary compact lower-value input for gledger59 clipped source upper-sum and original stopped-source gledger53. No continuity at zero or global lower value growth assumed.

import Mathlib
open Set
noncomputable section

theorem AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
    (a b : ℝ) (hab : a ≤ b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : ℝ, a ≤ y → y ≤ b → -B ≤ w y := by sorry
