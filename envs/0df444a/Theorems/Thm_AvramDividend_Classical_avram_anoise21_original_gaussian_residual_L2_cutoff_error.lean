-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise21_original_gaussian_residual_L2_cutoff_error
-- name    : AvramDividend.Classical.avram_anoise21_original_gaussian_residual_L2_cutoff_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:36:17.092092+00:00
-- url     : https://prove2.me/theorems/41b16fe8-15a4-4a36-ba1a-de58551cec32
-- title:
--   Original residual L2 approximation error at finite Gaussian cutoff
-- statement:
--   For the original-filtration measurable intrinsic residual R and original finite-cutoff approximants, the mean squared cutoff error is at most two over (n+1)^2 times twice the squared physical expected negative-jump count rate plus the rate. This quantitative original same-space L2 convergence avoids large jump first absolute moments.
-- source:
--   Combine Proved original limit cutoff bound anoise20 with Proved original total negative-jump count L2 anoise18 by squared triangle domination; directly supports original Gaussian bracket passage and martingale L1 limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise20_original_gaussian_residual_limit_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise21_original_gaussian_residual_L2_cutoff_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hRsource : ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
      atTop (nhds (R T ω)))
    (hRmeas : AEStronglyMeasurable (R T) P)
    (hCutMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) P) :
    ∀ n : ℕ,
      Integrable (fun ω =>
        (R T ω - avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2) P ∧
      (∫ ω, (R T ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2 ∂P) ≤
        2 * (1 / ((n : ℝ) + 1)) ^ 2 *
          (2 * (((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) ^ 2 +
            ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by sorry
