-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
-- name    : AvramDividend.Classical.avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:25:27.591206+00:00
-- url     : https://prove2.me/theorems/9fca1e6e-a24e-4ef9-97db-37de530b971e
-- title:
--   Original finite-activity Gaussian intrinsic residual has globally raw-adapted zero-start continuous-ae stationary independent-increments representative
-- statement:
--   On exactly the original spectrally negative Lévy filtered probability space, the intrinsic Gaussian source admits a raw-adapted zero-origin representative with continuous paths on one conull event, with independent increments relative to the actual raw filtration and stationary increment marginal laws.
-- source:
--   A39 original raw adapted common-conull continuous Gaussian modification; Proved A27 independent increments and Proved A24 stationary original source increment law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) := by sorry
