-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:38:18.316469+00:00
-- url     : https://prove2.me/theorems/8ad36659-6132-49f8-a757-9c0f1b52d874
-- title:
--   Finite-activity original source cutoffs converge to their physical limit uniformly on compact horizons
-- statement:
--   The original finite-negative-jump-activity Lévy source has a simultaneous physical time limit of its compensated negative-mark cutoffs and, on one common full-measure event, the convergence is uniform on every bounded clock interval. It can be evaluated at ruin-clipped random stopping times without a random-clock limiting interchange. Adaptedness and L1 conditional martingale centring remain separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_uniform_compact_ae

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      ∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω)
            atTop (𝓝 (G T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
                G T ω| ≤ η) := by sorry
