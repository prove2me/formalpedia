-- Prove2me | Theorems.Thm_AvramDividend_Classical_small_negative_jump_truncation_integrable
-- name    : AvramDividend.Classical.small_negative_jump_truncation_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T22:54:36.209349+00:00
-- url     : https://prove2.me/theorems/dbe0f093-01b7-4949-b81e-07b4996f9b80
-- title:
--   Finite truncated magnitude of small negative Lévy jumps from bounded variation
-- statement:
--   On the negative-jump interval (-1,0), min(-y,1) equals |y|. Consequently the bounded-variation integrability assumption ∫_{(-1,0)}|y|ν(dy)<∞ implies finite integral of the truncated positive jump magnitude on the small-jump interval. This gives the small-jump half of the finite truncated-first-moment condition for the pushforward renewal jump measure.
-- source:
--   Canonical Classical SpectrallyNegativeLevy.BoundedVariation.2 and pinned Mathlib setLIntegral_congr_fun

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- On small negative jumps, truncating the positive jump magnitude at one
agrees with the BV finite-variation absolute-value integrand. -/
theorem small_negative_jump_truncation_integrable (ν : Measure ℝ)
    (hBV : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) < ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal (min (-y) 1) ∂ν) < ⊤ := by
  sorry

end AvramDividend.Classical
