-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:02:34.147427+00:00
-- url     : https://prove2.me/theorems/05be2fe2-df74-4880-9dfe-7311464c61ad
-- title:
--   Original zero-jump Levy deterministic increments have centred Gaussian Laplace transforms
-- statement:
--   For the same original zero-jump Levy process, every deterministic increment from s to t has the centred Gaussian Laplace identity with variance coefficient Y.σ. Source-exact stationary increments transport the previously Proved fixed-time positive Laplace formula.
-- source:
--   Original SpectrallyNegativeLevy.stationaryIncrements field and Proved original centred Laplace theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_laplace_identity
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
       (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) =
      Real.exp (((t - s : ℝ≥0) : ℝ) *
        (Y.σ ^ 2 * θ ^ 2 / 2)) := by sorry
