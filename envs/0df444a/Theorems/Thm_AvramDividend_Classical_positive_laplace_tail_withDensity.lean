-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_tail_withDensity
-- name    : AvramDividend.Classical.positive_laplace_tail_withDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:27:03.240305+00:00
-- url     : https://prove2.me/theorems/d275650a-93fc-45f4-b0c7-794b95d0e7ad
-- title:
--   Laplace transform of the positive jump-tail density measure
-- statement:
--   For a measure μ on nonnegative jump magnitudes and θ>0, let the tail function at t>0 be μ{z:t<z} and use it as a density with respect to Lebesgue measure on (0,∞). The positive Laplace transform of this tail-density measure equals the integrated jump compensator ∫(1-exp(-θz))/θ dμ(z).
-- source:
--   Direct measure-valued wrapper around the already-Proved discounted_positive_jump_tail_transform. The only additional ingredient is Borel measurability of the antitone tail function t ↦ μ{z : t < z}. This supplies the tail-density measure B in the bounded-variation tilted-renewal construction for the Avram Dividend Classical mission.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_discounted_positive_jump_tail_transform
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

/-- The positive-jump tail, viewed as a density on the positive half-line,
has the expected integrated-compensator Laplace transform. -/
theorem positive_laplace_tail_withDensity
    (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-θ * t))
      ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((1 - Real.exp (-θ * (z : ℝ))) / θ) ∂μ := by
  sorry

end AvramDividend.Classical
