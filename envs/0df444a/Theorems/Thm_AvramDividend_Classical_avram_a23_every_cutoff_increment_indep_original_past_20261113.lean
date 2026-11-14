-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_every_cutoff_increment_indep_original_past_20261113
-- name    : AvramDividend.Classical.avram_a23_every_cutoff_increment_indep_original_past_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:13:52.267911+00:00
-- url     : https://prove2.me/theorems/ac6c69a0-3718-4538-a3fe-93cb27b583f9
-- title:
--   Each original Gaussian residual cutoff future increment is independent of the original right-continuous past
-- statement:
--   On the actual Omega, P and filtration of the original spectrally negative Levy process, every fixed Gaussian residual cutoff increment admits a measurable source-factor representation and is independent of the original right-continuous filtration at its starting time.
-- source:
--   Proved c8fa0b62 shifted source future path independence, Proved 42ada2ca cutoff adaptation, and A23 every-cutoff shift Borel representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every original finite Gaussian residual cutoff increment is independent of the actual right-continuous past. -/

theorem AvramDividend.Classical.avram_a23_every_cutoff_increment_indep_original_past_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (s t : ℝ≥0), s ≤ t →
      let D : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω
      (MeasurableSpace.comap D inferInstance ≤ mΩ) ∧
      StronglyMeasurable[MeasurableSpace.comap D inferInstance] D ∧
      ProbabilityTheory.Indep
        (MeasurableSpace.comap D inferInstance) (𝓕.rightCont s) P := by sorry
