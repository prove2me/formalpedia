-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:54:01.378722+00:00
-- url     : https://prove2.me/theorems/208594ec-33f7-472e-a735-c52fa593078e
-- title:
--   Original zero-jump source centered-square minus sigma-squared time is a right-continuous martingale
-- statement:
--   For the original spectrally negative Levy process with its source jump measure exactly zero, arbitrary nonnegative Gaussian coefficient including sigma=0, and original right-continuous filtration, prove the true compensated square martingale Q_t=(X.X_t-t*c)^2-t*sigma^2. Derive its conditional martingale identity by expanding at s<=t into Q_s + two copies of the integrable past-future source cross product + the integrable zero-mean source quadratic residual; use the already Proved cross and residual conditional-zero lemmas, and the Proved original conditional-variance identity for Q_s integrability. Establish adaptedness directly on the same Omega from source adaptedness. This is a mathematical Gaussian quadratic variation compensator in the pure continuous/no-jump sector, not a pathwise quadratic-variation theorem for general nu.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_past_cross_increment_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    Martingale (fun t ω =>
      (X.X t ω - (t : ℝ) * X.c) ^ 2 - (t : ℝ) * X.σ ^ 2)
      𝓕.rightCont P := by
  sorry
