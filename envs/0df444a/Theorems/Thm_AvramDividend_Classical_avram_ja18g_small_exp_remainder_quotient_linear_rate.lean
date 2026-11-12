-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_small_exp_remainder_quotient_linear_rate
-- name    : AvramDividend.Classical.avram_ja18g_small_exp_remainder_quotient_linear_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:57:41.476092+00:00
-- url     : https://prove2.me/theorems/fc9018a9-c1e4-4afb-8ba1-0f4f1118486d
-- title:
--   Original small negative compensated exponential quotient has explicit linear bound
-- statement:
--   For the original Levy measure, find a finite nonnegative K such that 0<θ≤1 implies the compensated small-jump exponential integral divided by θ is bounded above by θK. Use the Proved finite small-negative squared moment and pointwise quadratic compensated exponential inequality. This is the sharp quantitative version of the previously proved uniform bound; it yields the quotient-zero limit by squeeze with nonnegativity of exp u−1−u.
-- source:
--   J-A18 small jump derivative quantitative rate

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_small_exp_remainder_quotient_linear_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫ z in Ioo (-1 : ℝ) 0,
        Real.exp (θ * z) - 1 - θ * z ∂X.ν) / θ ≤ θ * K := by sorry
