-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:04:18.241198+00:00
-- url     : https://prove2.me/theorems/3a9ebf2b-4a45-43b1-86ff-d5a784ca6bff
-- title:
--   Same-space finite-activity Gaussian residual admits a compact-uniform original-filtration AE-adapted field
-- statement:
--   Remove the provisional per-cutoff measurability assumption from the Proved a70e016c limit theorem, using actual source-adaptedness for every truncated residual. Yield one original-space uniform-compact limit field whose every deterministic horizon is almost-everywhere measurable in the original right-continuous filtration. The finite-activity ν assumption is retained. This resolves adaptedness only, leaving Gaussian martingale centring, continuity, σ²t bracket and cross-orthogonality as remaining physical source obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_intrinsic_limit_ae_rightCont_measurable_of_cutoffs
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
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
