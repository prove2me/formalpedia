-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
-- name    : AvramDividend.Classical.avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:11:11.707898+00:00
-- url     : https://prove2.me/theorems/a70e016c-54c1-4cfc-8e42-9152dedaee9e
-- title:
--   Intrinsic Gaussian residual limit is right-continuous-filtration AE-measurable if each physical cutoff is adapted
-- statement:
--   Upgrade the Proved same-space compact-uniform residual limit to an almost-everywhere adapted limit under the explicit, source-specific measurability of each intrinsic truncated residual at each deterministic time. The theorem isolates the missing cutoff-adaptedness obligation; it does not assume an auxiliary independent Brownian process or claim continuity, centring or quadratic bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCut : ∀ (n : ℕ) (T : ℝ≥0),
      Measurable[𝓕.rightCont T]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
                R T ω| ≤ η)) ∧
      (∀ T : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont T] (R T) P) := by sorry
