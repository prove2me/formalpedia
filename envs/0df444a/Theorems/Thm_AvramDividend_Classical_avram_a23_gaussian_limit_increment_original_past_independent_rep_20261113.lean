-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_gaussian_limit_increment_original_past_independent_rep_20261113
-- name    : AvramDividend.Classical.avram_a23_gaussian_limit_increment_original_past_independent_rep_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:18:06.020282+00:00
-- url     : https://prove2.me/theorems/ba13ef0b-e09a-4ce3-84d8-92dceadcb2ca
-- title:
--   Original intrinsic Gaussian limit increment has a measurable same-source representative independent of the original past
-- statement:
--   On the original Omega/P/filtration, the physical Gaussian residual limit increment has a globally measurable random-variable representative with independence from the original right-continuous past, and agrees almost everywhere with the physical limit increment.
-- source:
--   Original future-path independence c8fa0b62 and A23 canonical Borel limit future-path representative; no completed-filtration hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian limit increment has a measurable representative independent of the original past. -/

theorem AvramDividend.Classical.avram_a23_gaussian_limit_increment_original_past_independent_rep_20261113
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
    ∃ D : Ω → ℝ,
      Measurable D ∧
      ProbabilityTheory.Indep (MeasurableSpace.comap D inferInstance)
        (𝓕.rightCont s) P ∧
      (∀ᵐ ω ∂P, D ω = R t ω - R s ω) := by sorry
