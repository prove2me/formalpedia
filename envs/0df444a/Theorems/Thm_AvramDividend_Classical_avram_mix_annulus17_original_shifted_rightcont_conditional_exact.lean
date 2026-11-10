-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus17_original_shifted_rightcont_conditional_exact
-- name    : AvramDividend.Classical.avram_mix_annulus17_original_shifted_rightcont_conditional_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:59:40.285545+00:00
-- url     : https://prove2.me/theorems/5bb8fe6e-57b1-47da-aa64-a95cdcbdcbb4
-- title:
--   Original shifted negative-annulus count has exact conditional mean and variance on right-continuous filtration
-- statement:
--   For the unchanged original spectrally negative Lévy process, the negative-annulus count over a deterministic future interval has conditional centred mean zero and conditional variance equal to elapsed time times its genuine Lévy measure, given the original right-continuous history. Both physical moments and integrability are independently obtained from the original zero-origin annulus variance, stationary marked-count distribution and one-cell original predictable compensation; no auxiliary Poisson construction is introduced. This is the missing quantitative prerequisite for source-exact predictable finite-grid annulus isometry, small-jump L2 convergence and the mixed infinite stopped source witness.
-- source:
--   Proved 6e234a3f, 34cdb144, 963870c8, 354411f0, 4208c6b2. Consumer 66ac8bb6 then original mixed source 5f12c023.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus17_original_shifted_rightcont_conditional_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P]
      (fun _ => r)) := by sorry
