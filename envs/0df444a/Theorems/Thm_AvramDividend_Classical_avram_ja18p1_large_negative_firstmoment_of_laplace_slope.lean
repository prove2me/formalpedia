-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1_large_negative_firstmoment_of_laplace_slope
-- name    : AvramDividend.Classical.avram_ja18p1_large_negative_firstmoment_of_laplace_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:20:20.929378+00:00
-- url     : https://prove2.me/theorems/222788b6-1c52-464c-9704-7a455c05488e
-- title:
--   Finite negative large-mark first moment from a finite lower Laplace slope
-- statement:
--   Pure Lévy-Khintchine analytic implication: if the original ψ(θ)/θ is bounded below for 0<θ≤1, the negative-large-mark first absolute ν-moment is finite, using the nonnegative small-jump exponential remainder and Fatou as θ↓0.
-- source:
--   J-A18 original Gaussian residual P first-moment target 887ac2d6, separates Lévy-measure analytic Fatou step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1_large_negative_firstmoment_of_laplace_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ)
    (hSlope : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      -C ≤ laplaceExponent X.c X.σ X.ν θ / θ) :
    (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) < ⊤ := by sorry
