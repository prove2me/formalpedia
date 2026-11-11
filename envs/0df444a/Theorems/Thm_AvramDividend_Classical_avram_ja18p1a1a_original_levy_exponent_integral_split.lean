-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1a1a_original_levy_exponent_integral_split
-- name    : AvramDividend.Classical.avram_ja18p1a1a_original_levy_exponent_integral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:02:41.755844+00:00
-- url     : https://prove2.me/theorems/b137b250-2290-40bd-80d6-fb72e9c3da61
-- title:
--   Exact original Levy exponent kernel partition at negative unit jump
-- statement:
--   Partition the original spectrally negative compensated Laplace kernel over Iio 0 into Ioo(-1,0) and Iic(-1), preserving the strict compensation endpoint and proving integrability from original Levy measure. This is the measure-theoretic split needed for the large-tail exponent identity.
-- source:
--   J-A18 original P1A1 child 8b66b99d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1a1a_original_levy_exponent_integral_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ z in Iio (0 : ℝ),
      (Real.exp (θ * z) - 1 -
        θ * z * (Ioo (-1 : ℝ) 1).indicator 1 z) ∂X.ν) =
      (∫ z in Ioo (-1 : ℝ) 0,
        (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) +
      (∫ z in Iic (-1 : ℝ),
        (Real.exp (θ * z) - 1) ∂X.ν) := by sorry
