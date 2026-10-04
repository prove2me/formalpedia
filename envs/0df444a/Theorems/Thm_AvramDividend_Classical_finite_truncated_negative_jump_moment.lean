-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_truncated_negative_jump_moment
-- name    : AvramDividend.Classical.finite_truncated_negative_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T22:55:45.208423+00:00
-- url     : https://prove2.me/theorems/05eba094-219c-42f9-b4a0-0e06e4475a7e
-- title:
--   Finite truncated absolute jump magnitude under BV and Lévy measure integrability
-- statement:
--   For a measure on real jumps with finite Lévy quadratic-truncation integral and finite first absolute moment of small negative jumps, the total integral over negative jumps of min(-y,1) is finite. Split (-∞,0) disjointly into jumps at most -1 and jumps between -1 and 0. The large-jump mass is finite by the Lévy integrability condition and the small-jump term by bounded variation. This is the precise intermediate condition used when mapping negative jumps into positive jump magnitudes for the positive renewal kernel.
-- source:
--   Canonical Classical SpectrallyNegativeLevy.ν_integrable, X.BoundedVariation.2, pinned Mathlib lintegral_union

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Small-jump bounded variation and large-jump Lévy integrability together
make the truncated absolute size of all negative jumps integrable. -/
theorem finite_truncated_negative_jump_moment (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hBV : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) < ⊤) :
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min (-y) 1) ∂ν) < ⊤ := by
  sorry

end AvramDividend.Classical
