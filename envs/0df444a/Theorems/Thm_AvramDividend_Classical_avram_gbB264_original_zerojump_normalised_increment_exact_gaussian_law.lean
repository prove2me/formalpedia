-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
-- name    : AvramDividend.Classical.avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:20:53.662642+00:00
-- url     : https://prove2.me/theorems/3e682259-c79e-4b1f-a823-124e4ce57182
-- title:
--   avram gbB264 original normalised gaussian law
-- statement:
--   For an original spectrally negative Levy process with zero jump measure and strictly positive Gaussian coefficient, each normalised drift-centred deterministic source increment has the exact centred Gaussian real distribution of variance t-s. This explicitly preserves the original sample space, original filtration and original Levy process. It follows from already Proved original MGF and exponential integrability plus generic positive MGF uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map (fun ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) P =
      gaussianReal 0 (t - s) := by sorry
