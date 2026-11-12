-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb40_compact_hessian_absolute_bound
-- name    : AvramDividend.Classical.avram_gb40_compact_hessian_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:28:09.460461+00:00
-- url     : https://prove2.me/theorems/f239e81c-28c1-4a0b-86b3-8943161d14d8
-- title:
--   Continuous second derivatives have a uniform absolute bound on compact real intervals
-- statement:
--   For a real function whose second iterated derivative is continuous on a nonempty closed bounded real interval, there is a single nonnegative constant bounding the absolute second derivative everywhere on that interval. This is the deterministic compact-Hessian ingredient of the original finite-cap Gaussian fourth-moment bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_gb40_compact_hessian_absolute_bound
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn (fun y => |iteratedDeriv 2 w y|) (Icc a b)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc a b, |iteratedDeriv 2 w y| ≤ B := by
  sorry
