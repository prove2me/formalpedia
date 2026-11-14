-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
-- name    : AvramDividend.Classical.avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:40:00.632133+00:00
-- url     : https://prove2.me/theorems/9e32027d-e62a-429f-a288-09166f8899c6
-- title:
--   Coherent original Gaussian limit future increments are globally measurable and independent of original past
-- statement:
--   At every deterministic time, one coherent original-source Borel representative of the Gaussian limit increment is measurable, independent of the original right-continuous past, and agrees with the physical Gaussian residual limit on one conull all-times event.
-- source:
--   A24 common Borel Gaussian limit future-path functional and Proved c8fa0b62 original future-path independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One coherent source representation of Gaussian increments is measurable and independent at every start. -/

theorem AvramDividend.Classical.avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
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
    ∃ D : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (D s)) ∧
      (∀ s, ProbabilityTheory.Indep
        (MeasurableSpace.comap (D s) inferInstance)
        (𝓕.rightCont s) P) ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        D s ω = R (s + T) ω - R s ω) := by sorry
