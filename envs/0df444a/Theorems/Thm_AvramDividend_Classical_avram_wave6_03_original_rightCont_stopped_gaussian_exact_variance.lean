-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:09:55.689654+00:00
-- url     : https://prove2.me/theorems/3c7623a6-ce31-4f8a-adc6-d73b0ebd8747
-- title:
--   Exact original-source stopped Gaussian drift-centred variance, including sigma zero
-- statement:
--   For the genuine original spectrally negative Lévy process X with zero jump measure, a bounded stopping time in the original right-continuous filtration and arbitrary Gaussian scale sigma (including zero), the true drift-centred stopped increment X_(tau+h)-X_tau-h c has exact real second moment h sigma squared. This closes the lower bound missing from earlier Fatou estimates, using the already Proved original-source exponential quotient exact energy and true-increment real L2 convergence. It is a finite-cell pure-Gaussian variance identity, not a claim that a general-jump source has continuous bracket or a full Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (h : ℝ) * X.σ ^ 2 := by
  sorry
