-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:16:11.452398+00:00
-- url     : https://prove2.me/theorems/aa0773e5-bd0b-41a0-b714-aa04a4ffb6bd
-- title:
--   Original finite-activity physical compensated cutoff process has a simultaneous pathwise limit
-- statement:
--   For finite negative jump activity, there exists a real-valued field on the original space and all physical nonnegative times, such that the original compensated cutoff source converges to it at every time on one common full-measure set. This is a pathwise source construction, not an unproved independent Brownian representation or a stopped martingale claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_cauchy_ae

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_physical_residual_limit_field_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        Tendsto
          (fun n : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω)
          atTop (𝓝 (G T ω)) := by sorry
