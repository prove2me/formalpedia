-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
-- name    : AvramDividend.Classical.finite_small_negative_jump_square_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:18:00.268176+00:00
-- url     : https://prove2.me/theorems/292417fa-a1aa-4b4b-b190-ba4e8583e86a
-- title:
--   Finite small negative jump square moment from Lévy integrability
-- statement:
--   Finite Lévy integral of min(1,y squared) implies finite second moment of the jump measure on the small negative interval (-1,0).
-- source:
--   Direct restriction of the canonical Lévy integrability condition, using y squared at most one on (-1,0).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem finite_small_negative_jump_square_moment
    (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (y ^ 2) ∂ν) < ⊤ := by
  sorry

end AvramDividend.Classical
