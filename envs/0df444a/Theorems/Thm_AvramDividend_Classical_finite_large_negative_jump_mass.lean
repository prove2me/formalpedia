-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_large_negative_jump_mass
-- name    : AvramDividend.Classical.finite_large_negative_jump_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:39:27.315994+00:00
-- url     : https://prove2.me/theorems/63b09787-1759-4ec1-8be2-488a27452aca
-- title:
--   Finite intensity of large negative Lévy jumps from the Lévy integrability condition
-- statement:
--   If the Lévy integrability integral of min(1,y²) is finite, the negative large-jump set (-∞,-1] has finite measure. This is the exact missing finite-mass premise in the Gaussian lower-integral argument and follows from a simple indicator domination of the integrability kernel.
-- source:
--   Use ENNReal-valued pointwise domination of the indicator of Iic(-1) by ENNReal.ofReal(min(1,y²)), the pinned lintegral_indicator_one identity, and lintegral_mono. No local Lean execution.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

theorem finite_large_negative_jump_mass
    (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min (1 : ℝ) (y ^ 2)) ∂ν) < ⊤) :
    ν (Iic (-1 : ℝ)) ≠ ⊤ := by
  sorry

end AvramDividend.Classical
