-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
-- name    : AvramDividend.Classical.avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:59:33.270166+00:00
-- url     : https://prove2.me/theorems/2ee4bc0f-cc77-4e13-818a-4f447061f478
-- title:
--   Actual Gaussian zerojump source normalised positive exponential cell-tail integrable
-- statement:
--   For an original zerojump spectrally negative Gaussian Lévy process, any nonnegative exponential tilt of the actual normalised centred increment remains integrable when restricted to a measurable one-sided large-increment event. This provides the authentic Gaussian integrability prerequisite for original a221/a224 and a216 rare-cell estimates.
-- source:
--   Original source Gaussian exponential integrability theorem a68, X.adapted exact Lévy process measurability

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ δ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      let Z : ℝ := ((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
      if δ ≤ Z then Real.exp (θ * Z) else 0) P := by sorry
