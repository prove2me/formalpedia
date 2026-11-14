-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB265_original_zerojump_unscaled_increment_gaussian_law
-- name    : AvramDividend.Classical.avram_gbB265_original_zerojump_unscaled_increment_gaussian_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:25:38.191543+00:00
-- url     : https://prove2.me/theorems/c2b8e8da-67b2-4f93-b31e-1ead03d97133
-- title:
--   Original zero-jump Levy source future increments have exact Gaussian drift and variance law
-- statement:
--   For every actual original zero-jump spectrally negative Levy process with positive Gaussian coefficient, the deterministic future source increment has a Gaussian law with mean drift times elapsed time and variance volatility squared times elapsed time. This source-faithful distribution identity is obtained by already proved original normalised MGFs and exponential-integrability, positive-ray MGF uniqueness, and Mathlib Gaussian scaling and translation. It feeds directly into the fixed-level good-dividend-cell Gaussian hitting estimate B261 and original finite-cap occupation B100.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB265_original_zerojump_unscaled_increment_gaussian_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map (fun ω => X.X t ω - X.X s ω) P =
      gaussianReal (((t - s : ℝ≥0) : ℝ) * X.c)
        ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * ((t - s : ℝ≥0) : NNReal)) := by sorry
