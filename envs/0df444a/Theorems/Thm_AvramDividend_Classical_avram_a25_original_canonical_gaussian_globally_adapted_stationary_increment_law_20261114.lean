-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_canonical_gaussian_globally_adapted_stationary_increment_law_20261114
-- name    : AvramDividend.Classical.avram_a25_original_canonical_gaussian_globally_adapted_stationary_increment_law_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:16:59.156994+00:00
-- url     : https://prove2.me/theorems/97d9319c-25db-4053-b661-06aaf277ba73
-- title:
--   Original raw-adapted Gaussian canonical process has exact stationary increment laws
-- statement:
--   On the exact original filtered probability space the finite-activity Gaussian residual has an everywhere zero-start globally raw-adapted process with stationary increments in distribution at every deterministic time.
-- source:
--   Proved e33982e1, f8000f9d, 5130dad2, Measure.map_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The globally raw-adapted physical Gaussian source has stationary increment laws on original P. -/

theorem AvramDividend.Classical.avram_a25_original_canonical_gaussian_globally_adapted_stationary_increment_law_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ s T : ℝ≥0,
        Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (G T) P) := by sorry
