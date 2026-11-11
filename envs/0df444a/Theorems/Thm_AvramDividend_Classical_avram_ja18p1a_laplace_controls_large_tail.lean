-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1a_laplace_controls_large_tail
-- name    : AvramDividend.Classical.avram_ja18p1a_laplace_controls_large_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:34:32.452194+00:00
-- url     : https://prove2.me/theorems/b0d050e0-f7bc-4bba-862d-fb1ee4928dc2
-- title:
--   Large negative exponential tail controlled by original Laplace slope
-- statement:
--   For a spectrally negative Levy process, the negative-large-jump exponential integral is bounded by a finite drift and small-jump variance constant minus the original Laplace exponent slope. Retains original ν, c, σ; uses finite second-moment Levy measure near 0.
-- source:
--   J-A18 necessary analytic source child of Open 222788b6 (first moment from bounded lower Laplace slope).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1a_laplace_controls_large_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ D : ℝ, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂X.ν) ≤
        ENNReal.ofReal (D - laplaceExponent X.c X.σ X.ν θ / θ) := by sorry
