-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_origin_crossing_strip_integral
-- name    : AvramDividend.Classical.negative_jump_origin_crossing_strip_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:16:20.72028+00:00
-- url     : https://prove2.me/theorems/6ab6c8c7-b350-4eef-8738-26f392429273
-- title:
--   Quadratic integrated size of the origin-crossing boundary strip
-- statement:
--   For any negative jump y, integrating its magnitude |y| over the positive-state interval (0,-y), where the jump crosses the scale-function origin, gives exactly y². This quantifies how a first-order origin-crossing jump contribution becomes second-order after state integration, enabling Fubini via the Lévy quadratic moment even when the first jump moment diverges.
-- source:
--   Lebesgue volume of a real interval and the boundary-layer contribution to the Avram Dividend generator calculation.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem negative_jump_origin_crossing_strip_integral
    (y : ℝ) (hy : y < 0) :
    (∫ x in Ioo (0 : ℝ) (-y), (-y)) = y ^ 2 := by sorry

end AvramDividend.Classical
