-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise24_original_cutoff_square_expectations_converge
-- name    : AvramDividend.Classical.avram_anoise24_original_cutoff_square_expectations_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T09:12:49.540625+00:00
-- url     : https://prove2.me/theorems/bd9da98e-7425-4074-9b43-e5b24954ddae
-- title:
--   Original Gaussian cutoff square expectations converge to physical residual square expectation
-- statement:
--   Under finite original negative-jump intensity, if the intrinsic physical Gaussian cutoff residuals converge almost surely to R, all cutoffs are measurable, and one cutoff square is integrable, then the expectations of the cutoff squares converge to the expectation of R squared. The proof dominates all cutoff squares by three times the sum of the original zero-cutoff square, the physical total negative-jump count square and the deterministic rate square. This supports exact sigma-squared bracket closure from the finite-cutoff source variance formula.
-- source:
--   Root-connected analytic bridge from accepted original pathwise cutoff bound 1b696ff5 and original total negative count L2 a6562a4d to 892afa4a, requiring only one finite-cutoff square-integrability premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise19_original_gaussian_residual_cutoff_count_bound
import Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_total_negative_count_finite_activity_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise24_original_cutoff_square_expectations_converge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hRsource : ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
      atTop (nhds (R T ω)))
    (hCutMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) P)
    (hCutSquare : Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P) :
    Tendsto
      (fun n : ℕ => ∫ ω,
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω) ^ 2 ∂P)
      atTop (nhds (∫ ω, (R T ω) ^ 2 ∂P)) := by sorry
