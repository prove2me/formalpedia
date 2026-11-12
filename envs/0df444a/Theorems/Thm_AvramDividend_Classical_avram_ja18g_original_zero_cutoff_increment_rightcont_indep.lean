-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_zero_cutoff_increment_rightcont_indep
-- name    : AvramDividend.Classical.avram_ja18g_original_zero_cutoff_increment_rightcont_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T03:46:07.592501+00:00
-- url     : https://prove2.me/theorems/44150b04-fb86-435d-80c3-7cae47f48c1c
-- title:
--   Original zero-cutoff residual future increment independent of original right-continuous past
-- statement:
--   The original same-space Lévy process residual R0(t)-R0(s) has a measurable generated sigma-algebra and is independent of the original right-continuous past filtration at s; prove from original rightCont stationary independent increments of X and original measurable compensated jump path. Previous authoring job failed solely at unqualified Indep.
-- source:
--   J-A18 source-compatible repair of original conditional-independent increments

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_zero_cutoff_increment_rightcont_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ s t : ℝ≥0, s ≤ t →
      let D : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω
      (MeasurableSpace.comap D inferInstance ≤ mΩ) ∧
      StronglyMeasurable[MeasurableSpace.comap D inferInstance] D ∧
      ProbabilityTheory.Indep
        (MeasurableSpace.comap D inferInstance) (𝓕.rightCont s) P := by sorry
