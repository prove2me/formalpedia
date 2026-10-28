-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_scale_identity_to_ratio
-- name    : AvramDividend.Classical.stopped_scale_identity_to_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:25:30.540526+00:00
-- url     : https://prove2.me/theorems/212e3098-4410-47cc-8a4c-a70e6061351b
-- title:
--   Stopped scale identity implies the scale-function ratio
-- statement:
--   If an extended-nonnegative-real L satisfies L times ENNReal.ofReal va equals ENNReal.ofReal vx with 0 < va, then L equals ENNReal.ofReal (vx / va).
-- source:
--   Algebraic bridge isolating the final division step of the Proposition 1 two-sided-exit reduction: the stopped-scale identity (lintegral times ofReal (W a) equals ofReal (W x)) implies the ratio form once W a > 0. Pure ENNReal algebra, no stochastic content; reusable by the corrected two-sided-exit target.

import Mathlib

open scoped ENNReal

namespace AvramDividend.Classical

theorem stopped_scale_identity_to_ratio
    (L : ℝ≥0∞) (vx va : ℝ)
    (hL : L * ENNReal.ofReal va = ENNReal.ofReal vx)
    (hva : 0 < va) :
    L = ENNReal.ofReal (vx / va) := by sorry

end AvramDividend.Classical
