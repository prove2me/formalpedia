-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_scale_weighted_renewal_contraction
-- name    : AvramDividend.Classical.zero_scale_weighted_renewal_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:40:47.157502+00:00
-- url     : https://prove2.me/theorems/1c6281a8-51de-48c2-ad18-723953a9f7a2
-- title:
--   Zero-discount scale Laplace mass gives a strict positive-discount renewal contraction
-- statement:
--   For q≥0 and a Laplace exponent ψ(theta)>q, the exponentially weighted zero-scale kernel multiplied by q has total L1 mass q/ψ(theta), strictly less than one. This supplies the exact contraction needed to sum its positive Neumann convolution powers and construct the q-discounted scale from W0.
-- source:
--   Direct Laplace clause of IsScaleFunction X 0 W0 and elementary division inequality.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_scale_weighted_renewal_contraction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hqθ : q < X.ψ θ) :
    q * (∫ y in Ioi (0 : ℝ),
      Real.exp (-(θ * y)) * W₀ y ∂volume) < 1 := by sorry
