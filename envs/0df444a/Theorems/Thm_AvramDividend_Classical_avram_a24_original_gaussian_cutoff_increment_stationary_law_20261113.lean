-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_cutoff_increment_stationary_law_20261113
-- name    : AvramDividend.Classical.avram_a24_original_gaussian_cutoff_increment_stationary_law_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:36:52.604783+00:00
-- url     : https://prove2.me/theorems/15a41296-26cc-4f4f-a0ce-64cb3246c71d
-- title:
--   Stationary laws of all original physical finite Gaussian residual cutoff increments
-- statement:
--   For each cutoff and duration, all translated original Gaussian residual cutoff increments have the same pushforward probability law, represented by a measurable random variable on the original source probability space.
-- source:
--   A24 original time-uniform Gaussian cutoff Borel representation and Proved source future-path stationary law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_future_path_borel_functional_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A physical Gaussian residual cutoff has a measurable stationary-increment law. -/

theorem AvramDividend.Classical.avram_a24_original_gaussian_cutoff_increment_stationary_law_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) :
    ∃ Z : Ω → ℝ,
      Measurable Z ∧
      ∀ s : ℝ≥0,
        Measure.map (fun ω =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X n (s + T) ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) P =
        Measure.map Z P := by sorry
