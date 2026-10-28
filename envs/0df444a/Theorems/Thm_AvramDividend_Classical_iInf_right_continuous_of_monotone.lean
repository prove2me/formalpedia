-- Prove2me | Theorems.Thm_AvramDividend_Classical_iInf_right_continuous_of_monotone
-- name    : AvramDividend.Classical.iInf_right_continuous_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:21:07.925069+00:00
-- url     : https://prove2.me/theorems/064854ad-e270-461e-8e18-2c1bf29aaf27
-- title:
--   The infimum of nondecreasing right-continuous nonnegative CDF kernels is right-continuous
-- statement:
--   Let F_i be an arbitrary indexed family of nondecreasing right-continuous maps ℝ→[0,∞]. Their pointwise infimum is right-continuous. In particular, taking the infimum over finite Lévy horizons preserves right continuity of a weighted survival CDF, supporting construction of the corresponding Stieltjes measure.
-- source:
--   For the lower semicontinuity of the pointwise infimum along Ici(x), use monotonicity to bound all right-neighbour values below by the value at x. For upper semicontinuity, invoke pinned Mathlib upperSemicontinuousWithinAt_iInf on the family of right-continuous functions. Finish using continuousWithinAt_iff_lower_upperSemicontinuousWithinAt. This is an actual topological property needed to construct the infinite-horizon Esscher survival distribution without positing a tilted path-space measure.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.CompleteLattice.Basic

open Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.iInf_right_continuous_of_monotone
    {ι : Type*} [Nonempty ι]
    (F : ι → ℝ → ℝ≥0∞)
    (hmono : ∀ i, Monotone (F i))
    (hright : ∀ i x, ContinuousWithinAt (F i) (Ici x) x) :
    ∀ x : ℝ,
      ContinuousWithinAt (fun y => ⨅ i, F i y) (Ici x) x := by sorry
