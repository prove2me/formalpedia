-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1a1b_large_exp_lintegral_real_bridge
-- name    : AvramDividend.Classical.avram_ja18p1a1b_large_exp_lintegral_real_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:02:43.271034+00:00
-- url     : https://prove2.me/theorems/ca099cae-e333-409f-93a4-933a58bd8008
-- title:
--   Convert original large-negative exponential loss to real integral
-- statement:
--   On the original negative-large-mark region with finite Levy mass, 1-exp(theta*z) is nonnegative and integrable. Its ENNReal quotient lintegral equals ofReal of the signed real integral difference, divided by positive theta. Original ν and threshold endpoints retained.
-- source:
--   J-A18 original P1A1 child 8b66b99d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1a1b_large_exp_lintegral_real_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ z in Iic (-1 : ℝ),
      ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) =
      ENNReal.ofReal
        (- (∫ z in Iic (-1 : ℝ), (Real.exp (θ * z) - 1) ∂X.ν) / θ) := by sorry
