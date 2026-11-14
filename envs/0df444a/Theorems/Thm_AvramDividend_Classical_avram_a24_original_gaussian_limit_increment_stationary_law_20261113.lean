-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
-- name    : AvramDividend.Classical.avram_a24_original_gaussian_limit_increment_stationary_law_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:39:15.632927+00:00
-- url     : https://prove2.me/theorems/5130dad2-fea0-41d3-9ff1-3762f828ae1c
-- title:
--   Exact stationary laws for original Gaussian residual limit increments at all deterministic start times
-- statement:
--   The original physical intrinsic Gaussian residual limit increment over any fixed duration has the same pushforward law for all deterministic starting times, represented by a measurable source random variable.
-- source:
--   A24 uniform source Gaussian limit future-path Borel representation and Proved A23 source shifted future-path stationary law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_future_path_borel_functional_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original Gaussian residual limit increment of fixed duration has one stationary law. -/

theorem AvramDividend.Classical.avram_a24_original_gaussian_limit_increment_stationary_law_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (T : ℝ≥0) :
    ∃ Z : Ω → ℝ, Measurable Z ∧
      ∀ s : ℝ≥0,
        Measure.map (fun ω => R (s + T) ω - R s ω) P =
        Measure.map Z P := by sorry
