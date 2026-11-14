-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_gaussian_limit_increment_canonical_future_borel_20261113
-- name    : AvramDividend.Classical.avram_a23_gaussian_limit_increment_canonical_future_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:17:08.229207+00:00
-- url     : https://prove2.me/theorems/55a72e4c-ff63-4979-8bee-951255f1c647
-- title:
--   Intrinsic original Gaussian residual limit increment has a canonical Borel future-increment path representative
-- statement:
--   Every actual Gaussian cutoff limit increment admits a canonical measurable functional of the original future-increment path, equal to the prescribed original physical limit on a P-conull event, without adding noise or completing the filtration.
-- source:
--   Proved original compact source convergence 3a9ebf2b, A23 every-cutoff Borel representation and pinned-Mathlib default limUnder theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical Gaussian limit increment has a canonical measurable future-path representative. -/

theorem AvramDividend.Classical.avram_a23_gaussian_limit_increment_canonical_future_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ Wlim : (ℝ≥0 → ℝ) → ℝ,
      Measurable Wlim ∧
      (∀ᵐ ω ∂P,
        Wlim (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) =
          R t ω - R s ω) := by sorry
