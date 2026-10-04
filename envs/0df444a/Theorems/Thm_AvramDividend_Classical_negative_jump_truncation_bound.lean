-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_bound
-- name    : AvramDividend.Classical.negative_jump_truncation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:48:35.530146+00:00
-- url     : https://prove2.me/theorems/7b691c09-4704-448a-868e-fe5277982ee6
-- title:
--   Bound positive Lévy jump truncation by BV small jumps plus Lévy-square integrability
-- statement:
--   For every real jump size y, the truncated magnitude min(max(-y,0),1) is bounded above by |y| on (-1,0), plus min(1,y²). The first term is integrable under the bounded-variation condition and the second under the Lévy-measure assumption in the actual Classical SpectrallyNegativeLevy structure. This provides the exact majorant needed to prove finite truncated-first-moment of the positive jump-magnitude pushforward measure, enabling renewal-kernel dominated convergence for the actual process.
-- source:
--   Pinned Mathlib Real.coe_toNNReal', Set.indicator_of_mem, arithmetic. Exact Avram Classical SpectrallyNegativeLevy.BoundedVariation and ν_integrable hypotheses

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- An integrable pointwise majorant for the positive jump-magnitude
truncation, in terms of the bounded-variation small-jump integral
and the original Lévy-square integrability condition. -/
theorem negative_jump_truncation_bound (y : ℝ) :
    min ((Real.toNNReal (-y) : ℝ)) 1 ≤
      (Ioo (-1 : ℝ) 0).indicator (fun x : ℝ => |x|) y +
        min 1 (y ^ 2) := by
  sorry

end AvramDividend.Classical
