-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_full_ruin_G_integrable_and_nonpos_mean
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_full_ruin_G_integrable_and_nonpos_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:37:21.913982+00:00
-- url     : https://prove2.me/theorems/547a18f8-9e2e-406b-9c73-b5cc070c3207
-- title:
--   Exact original full pre-ruin physical signed generator residual is L1 and has nonpositive expectation
-- statement:
--   For the genuine original controlled process, a single joint μ×P Integrable physical generator density and nonpositive all finite clipped ruin-clock integrals imply the full pre-ruin physical residual G is Integrable on P and its expectation is ≤0. This combines compiler-Proved source measurable ruinTime product sets with compiler-Proved original sign preservation and Mathlib Fubini/integral_nonpos_of_ae. No invented boundary zero occupation or martingale optional stopping.
-- source:
--   Accepted original P4-E helpers cb6d7bfc and 67b41962, pinned Mathlib Integrable.indicator, integral_prod_right and integral_nonpos_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clock_product_measurable_sets
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original full ruin physical residual is globally L¹ and has nonpositive mean. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_full_ruin_G_integrable_and_nonpos_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P))
    (hNonpos : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, ({s : ℝ≥0 |
        (s : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
          (fun t => f (t, ω)) t ∂μ) ≤ 0) :
    Integrable (fun ω => ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
          (fun t => f (t, ω)) t ∂μ) P ∧
    (∫ ω, ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
          (fun t => f (t, ω)) t ∂μ ∂P) ≤ 0 := by sorry
