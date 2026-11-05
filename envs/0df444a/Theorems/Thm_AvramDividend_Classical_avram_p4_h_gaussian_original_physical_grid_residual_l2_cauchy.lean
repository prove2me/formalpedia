-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_physical_grid_residual_l2_cauchy
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_physical_grid_residual_l2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:06:15.030448+00:00
-- url     : https://prove2.me/theorems/5674a795-53f0-4910-9770-4bd962809f24
-- title:
--   Original Gaussian residual L2 Cauchy directly from physical finite-grid Lévy jump estimates
-- statement:
--   For the original Levy process X on exactly P and the original filtration, source squared-grid approximations for every cutoff pair with measurable physical grid, almost-sure intrinsic jump limit, original X.ν finite-grid second-moment bound, and original squared-band measurability imply the actual original Gaussian residual cutoff sequence is L2 Cauchy at each horizon. This assembles the accepted physical-grid-to-real-isometry and original residual Cauchy theorems without any invented source decomposition or independent Y.
-- source:
--   Proved source physical-grid-to-intrinsic real L2 f1020361-fcdb-4a3b-8780-dda7279d6c89 and Proved original residual L2 Cauchy from true source strip bound 48070cf0-80bd-40b6-9c87-18766861a473.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_grid_to_intrinsic_real_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_L2_cauchy_from_physical_strip_isometry
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_physical_grid_residual_l2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (G : ℕ → ℕ → ℕ → Ω → ℝ≥0∞)
    (hMeas : ∀ n m k, Measurable (G n m k))
    (hSourceLimit : ∀ n m, ∀ᵐ ω ∂P,
      Tendsto (fun k => G n m k ω) atTop
        (𝓝 (ENNReal.ofReal
          ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2))))
    (hSourceFiniteGrid : ∀ n m k,
      (∫⁻ ω, G n m k ω ∂P) ≤ (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν))
    (hSquareAE : ∀ n m, AEStronglyMeasurable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      Integrable (fun ω : Ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
      (∫ ω : Ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
         avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by sorry
