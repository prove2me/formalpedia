-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_fourth_moment_le_three_time_sq
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_fourth_moment_le_three_time_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:19:17.688816+00:00
-- url     : https://prove2.me/theorems/61114546-79b4-43da-9868-2efbe6e927a2
-- title:
--   Original normalised zero-jump Lévy fourth moment at most three times squared horizon
-- statement:
--   For the actual centred normalised fixed-time increment of an original ν=0 spectrally negative Lévy process, the fourth nonnegative moment is bounded by 3 times the square of time. Original positive exponential tilt Fatou, Gaussian dominated convergence and an exact Gaussian reference even-moment formula yield this bound. It is the quantitative increment estimate for compact Taylor large-increment L1 control, without a surrogate Brownian path.
-- source:
--   Public Proved 46e23cf2 original Fatou, Proved 9f1008a6 GaussianReal tilt DCT and Proved 76aa5b0b FeynmanWick.gaussianReal_moment_even.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_gaussianReal_fourth_positive_tilt_tendsto_zero
import Theorems.Thm_FeynmanWick_gaussianReal_moment_even

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_fourth_moment_le_three_time_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) (t : ℝ≥0)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X t ω - (t : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    ENNReal.ofReal (3 * (t : ℝ) ^ 2) := by sorry
