-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_fourth_moment_le_gaussian_reference
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_fourth_moment_le_gaussian_reference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:18:26.886727+00:00
-- url     : https://prove2.me/theorems/25c0fee6-4ed6-4423-904e-311f8cd8080a
-- title:
--   Original fixed-time Gaussian fourth moment controlled by Gaussian reference fourth moment
-- statement:
--   For the original zero-negative-jump Levy process with measurable centred normalized increment, the fourth nonnegative moment of the original increment is bounded by the fourth moment of the corresponding GaussianReal reference law. Combine original positive exponential tilt Fatou and two-sided Gaussian dominated convergence. This is the exact bridge needed before a quantitative O(h^2) large-increment Taylor L1 estimate, without asserting a detached Brownian source.
-- source:
--   Proved original positive-tilt Fatou 46e23cf2 and GaussianReal fourth positive-tilt convergence 9f1008a6; Mathlib ENNReal.continuous_ofReal and Filter.Tendsto.liminf_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_fourth_moment_le_gaussian_reference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) (t : ℝ≥0)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X t ω - (t : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    ENNReal.ofReal (∫ z : ℝ, z ^ 4 ∂(gaussianReal 0 t)) := by sorry
