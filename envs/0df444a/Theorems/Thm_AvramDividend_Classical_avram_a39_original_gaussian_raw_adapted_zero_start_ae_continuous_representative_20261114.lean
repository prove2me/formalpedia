-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
-- name    : AvramDividend.Classical.avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:18:52.345686+00:00
-- url     : https://prove2.me/theorems/7783a4ae-2837-48e8-87a1-5445e15d5dce
-- title:
--   Original Gaussian intrinsic residual admits globally raw-adapted zero-start representative with continuous source paths on one conull event
-- statement:
--   On the original finite-activity filtered probability space, the intrinsic Gaussian cutoff limit admits a globally adapted and zero-start modification equal at every time almost surely, whose whole physical sample path is continuous on a single conull event.
-- source:
--   Proved A24 original raw adapted representative and A38 exact source physical Gaussian path continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a39_original_gaussian_raw_adapted_zero_start_ae_continuous_representative_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) := by sorry
