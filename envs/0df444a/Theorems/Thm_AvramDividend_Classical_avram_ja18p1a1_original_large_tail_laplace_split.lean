-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1a1_original_large_tail_laplace_split
-- name    : AvramDividend.Classical.avram_ja18p1a1_original_large_tail_laplace_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:55:43.11813+00:00
-- url     : https://prove2.me/theorems/8b66b99d-072b-423e-858d-1ffb5cea4250
-- title:
--   Exact original Levy Laplace split of negative exponential tail
-- statement:
--   Use the original Levy-Khintchine exponent, disjoint decomposition Iio(0)=Iic(-1) union Ioo(-1,0), original finite large-negative mark mass and compensated small-band integrability. Identify the nonnegative large-mark exponential lintegral with the real difference of drift, Gaussian, small compensated term and original exponent. Exact same ν,c,sigma.
-- source:
--   Necessary child of J-A18 P1A b0d050e0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1a1_original_large_tail_laplace_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) (hθOne : θ ≤ 1) :
    (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) =
      ENNReal.ofReal
        (X.c + X.σ ^ 2 * θ / 2 +
          (∫ z in Ioo (-1 : ℝ) 0,
            (Real.exp (θ * z) - 1 - θ * z) ∂X.ν) / θ -
          laplaceExponent X.c X.σ X.ν θ / θ) := by sorry
