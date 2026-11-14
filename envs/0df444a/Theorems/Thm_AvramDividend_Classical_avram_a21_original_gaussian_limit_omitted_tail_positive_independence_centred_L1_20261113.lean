-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T10:14:58.381242+00:00
-- url     : https://prove2.me/theorems/84fe2800-60c4-4099-9b5d-879adbd4466e
-- title:
--   Positive-horizon original Gaussian-limit versus omitted-tail independence and source L1 centring
-- statement:
--   For the ORIGINAL Levy probability space at each positive horizon, the limiting Gaussian process R is independent of the OMITTED compensated negative mark tail Rn-R. Both source fields are integrable and the centred Gaussian field has zero expectation. This is a sound disjoint Brownian/Gaussian versus Poisson mark property and is strictly different from the false independence of the original zero-cutoff residual R0 and RETAINED negative jump band Jn.
-- source:
--   Original Levy-Ito same-space independent Gaussian component and disjoint marked Poisson small jump process, plus source Gaussian drift centring. Physical identity Rn=R+(Jsmall-Jn) Proved cb474bae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_independence_centred_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
      ProbabilityTheory.IndepFun (R t) J P ∧
        Integrable (R t) P ∧ Integrable J P ∧
        (∫ ω, R t ω ∂P) = 0 := by sorry
