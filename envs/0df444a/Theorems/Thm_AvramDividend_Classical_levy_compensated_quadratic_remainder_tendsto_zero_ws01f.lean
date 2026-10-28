-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_quadratic_remainder_tendsto_zero_ws01f
-- name    : AvramDividend.Classical.levy_compensated_quadratic_remainder_tendsto_zero_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:21:34.314989+00:00
-- url     : https://prove2.me/theorems/055a8ad7-8d69-4dfa-abf9-46e62300568f
-- title:
--   Actual Lévy small-negative-jump quadratic exponent remainder vanishes
-- statement:
--   For every actual spectrally negative Lévy process, the compensated small-negative-jump contribution to its positive Laplace exponent becomes negligible when divided by the square of integer Laplace parameter n+1. Uses only the canonical Lévy measure integrability, a previously accepted compensated-kernel theorem and the independently accepted general dominated-convergence lemma. This identifies the jump-free quadratic growth scale for the Gaussian branch, but does not assert path regularity.
-- source:
--   Lévy–Khintchine small-jump second moment and integrable compensated kernel; Prove2Me Proved finite_small_negative_jump_square_moment and levy_small_negative_compensated_div_integrable; WS1F quadratic-kernel theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_small_negative_jump_square_moment
import Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
import Theorems.Thm_AvramDividend_Classical_compensated_exp_quadratic_ratio_tendsto_zero_ws01f

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_quadratic_remainder_tendsto_zero_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      ∫ y in Ioo (-1 : ℝ) 0,
        (Real.exp (((n : ℝ) + 1) * y) - 1 -
          ((n : ℝ) + 1) * y) / (((n : ℝ) + 1) ^ 2) ∂X.ν)
      atTop (nhds 0) := by sorry
