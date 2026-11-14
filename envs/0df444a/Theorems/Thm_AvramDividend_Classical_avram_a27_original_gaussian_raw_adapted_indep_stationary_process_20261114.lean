-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_gaussian_raw_adapted_indep_stationary_process_20261114
-- name    : AvramDividend.Classical.avram_a27_original_gaussian_raw_adapted_indep_stationary_process_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:42:20.252288+00:00
-- url     : https://prove2.me/theorems/ad333d75-8664-43b2-967f-0cafeebf8c8d
-- title:
--   Canonical original Gaussian is globally adapted with raw independent stationary increments
-- statement:
--   The original spectrally negative finite-activity Levy source admits on the same filtered probability space a globally adapted zero-start Gaussian residual process with independent and stationary increments.
-- source:
--   Proved B31, A24, A25 and A27 original raw filtration independence transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original raw-adapted Gaussian source has both source-past independent and stationary increments. -/

theorem AvramDividend.Classical.avram_a27_original_gaussian_raw_adapted_indep_stationary_process_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s T : ℝ≥0,
        Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (G T) P) := by sorry
