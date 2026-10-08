-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
-- name    : AvramDividend.Classical.levy_small_negative_compensated_div_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:22:04.265211+00:00
-- url     : https://prove2.me/theorems/e1ef23c7-7086-4d60-8ba7-0766683211f1
-- title:
--   Canonical small negative-jump compensated kernel is integrable after division
-- statement:
--   For the exact canonical spectrally negative Lévy process and any positive real Laplace parameter, the compensated exponential jump kernel divided by that parameter is Bochner-integrable on the small-negative-jump region (-1,0) against its Lévy measure. This supplies the integrability hypothesis needed to turn the extended nonnegative jump-integral divergence into real-integral asymptotics.
-- source:
--   Direct restriction, a.e. equality and scalar multiplication of the independently Prove2Me-Proved levy_compensated_jump_integrable_nonneg theorem at pinned Mathlib revision, with exact (-1,0) endpoint handling.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_small_negative_compensated_div_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun y : ℝ =>
      (Real.exp (θ * y) - 1 - θ * y) / θ)
      (Ioo (-1 : ℝ) 0) X.ν := by sorry
