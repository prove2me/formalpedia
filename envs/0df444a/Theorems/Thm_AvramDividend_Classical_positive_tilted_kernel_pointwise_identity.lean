-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_tilted_kernel_pointwise_identity
-- name    : AvramDividend.Classical.positive_tilted_kernel_pointwise_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:38:40.625538+00:00
-- url     : https://prove2.me/theorems/3b9eae23-51ab-4b41-a678-72f7e315b4aa
-- title:
--   Pointwise ENNReal algebra for the positive tilted renewal kernel
-- statement:
--   For nonnegative tilt a, positive discount s and nonnegative jump magnitude z, the positive tail-transform contribution plus the weighted cumulative contribution equals the shifted compensator transform. This is the pointwise identity (1-e^{-sz})/s + e^{-sz}(1-e^{-az})/s = (1-e^{-(s+a)z})/s, expressed exactly in ENNReal.ofReal form.
-- source:
--   Elementary exponential and ENNReal algebra at pinned Mathlib 0df444a3. The nonnegativity hypotheses make ENNReal.ofReal_add and ENNReal.ofReal_mul exact. This is the algebraic core of the Avram bounded-variation tilted-renewal kernel transform.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- The tail and weighted-cumulative Laplace integrands combine into the
single shifted positive jump transform used by the tilted BV renewal kernel. -/
theorem positive_tilted_kernel_pointwise_identity
    (a s z : ℝ) (ha : 0 ≤ a) (hs : 0 < s) (hz : 0 ≤ z) :
    ENNReal.ofReal ((1 - Real.exp (-s * z)) / s) +
        ENNReal.ofReal (1 / s) *
          (ENNReal.ofReal (Real.exp (-s * z)) *
            ENNReal.ofReal (1 - Real.exp (-a * z))) =
      ENNReal.ofReal ((1 - Real.exp (-(s + a) * z)) / s) := by
  sorry

end AvramDividend.Classical
