-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
-- name    : AvramDividend.Classical.avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:10:40.640202+00:00
-- url     : https://prove2.me/theorems/0f0c5f37-8423-4dd6-a410-be40b4cc242c
-- title:
--   Original finite-activity positive-volatility Gaussian intrinsic residual has exact centred normal law with variance sigma squared times time
-- statement:
--   Prove under the original physical Levy source and uncompleted source filtration that any a.e.-all-time equivalent Gaussian intrinsic cutoff limit has exact centred Gaussian marginal law at time t with variance t*sigma^2. This requires the original-source Levy–Khintchine or marked Poisson decomposition and does not assume a zero-nu companion exists.
-- source:
--   Physical source finite-activity jump removal and original Levy–Khintchine Gaussian characteristic exponent; genuine analytic source law obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ t : ℝ≥0,
      HasLaw (G t)
        (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) P := by sorry
