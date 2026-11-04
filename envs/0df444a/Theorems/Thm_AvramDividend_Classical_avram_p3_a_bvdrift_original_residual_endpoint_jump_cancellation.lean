-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_residual_endpoint_jump_cancellation
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_endpoint_jump_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:21:59.251613+00:00
-- url     : https://prove2.me/theorems/85f7987a-9608-40a4-8ec5-ea806ed98c1d
-- title:
--   At every positive time the original BV canonical residual cancels the exact source endpoint jump
-- statement:
--   At every positive time on one original BV source full event, the drift-minus-source-path minus all negative jumps up to t equals drift-minus-the-actual-source-left-limit minus all strict-past jumps. The actual source endpoint jump cancels algebraically. This is a key pathwise no-jump identity, with no Poisson replacement and no zero-residual assumption.
-- source:
--   Proved actual source BV real endpoint jump-sum split b725a54d and ring algebra. Source leftLim and X.X remain unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_endpoint_split

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual original BV source's jump at t cancels exactly against
the identical endpoint atom removed from its canonical residual. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_endpoint_jump_cancellation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      (((t : ℝ) * X.drift - X.X t ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) =
      (((t : ℝ) * X.drift -
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) t) -
          (∑' u : ℝ≥0, if 0 < u ∧ u < t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
          else 0).toReal) := by sorry
