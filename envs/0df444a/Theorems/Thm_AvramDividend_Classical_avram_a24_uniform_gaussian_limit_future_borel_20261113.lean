-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_future_borel_20261113
-- name    : AvramDividend.Classical.avram_a24_uniform_gaussian_limit_future_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:37:44.181999+00:00
-- url     : https://prove2.me/theorems/f6c50e2f-614c-4252-b9c1-70ce8acbdf6d
-- title:
--   One original-source Borel Gaussian limit future-path functional works at every deterministic start time
-- statement:
--   For every fixed duration, the original physical Gaussian residual limit increment is a common globally measurable future-increment path functional at every deterministic starting time on one conull source event.
-- source:
--   A24 uniform every-cutoff future-path representation, A23 measurable default limit, original all-time conull Gaussian cutoff convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a23_measurable_real_sequence_limit_default_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One globally Borel future-path functional represents all original Gaussian limit increments of a given duration. -/

theorem AvramDividend.Classical.avram_a24_uniform_gaussian_limit_future_borel_20261113
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
    ∃ Wlim : (ℝ≥0 → ℝ) → ℝ, Measurable Wlim ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        Wlim (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) =
          R (s + T) ω - R s ω) := by sorry
