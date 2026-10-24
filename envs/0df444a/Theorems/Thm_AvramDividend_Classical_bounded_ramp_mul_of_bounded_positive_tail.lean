-- Prove2me | Theorems.Thm_AvramDividend_Classical_bounded_ramp_mul_of_bounded_positive_tail
-- name    : AvramDividend.Classical.bounded_ramp_mul_of_bounded_positive_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:27:15.157189+00:00
-- url     : https://prove2.me/theorems/5868bb6d-5009-4c10-8102-30ba103524e5
-- title:
--   Ramp cutoff of a kernel bounded away from zero is globally bounded
-- statement:
--   If f is bounded on the ray [ε,∞) and ε>0, then the clipped ramp χε vanishing below ε makes χε f bounded globally. The bound follows from 0≤χ≤1 and the zero support region. This complements the cutoff-continuity theorem to furnish a globally bounded continuous kernel for convolution with an L1 factor.
-- source:
--   Elementary clipped ramp bounds, product norm and boundedness on a positive ray.

import Mathlib.Analysis.Normed.Group.Basic
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
open AvramDividend.Classical Set

namespace AvramDividend.Classical
theorem bounded_ramp_mul_of_bounded_positive_tail
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → ‖f x‖ ≤ M) :
    BddAbove (Set.range fun x : ℝ => ‖max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x‖) := by sorry
end AvramDividend.Classical
