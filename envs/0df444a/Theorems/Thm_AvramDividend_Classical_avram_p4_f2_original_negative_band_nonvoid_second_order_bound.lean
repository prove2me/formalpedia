-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_nonvoid_second_order_bound
-- name    : AvramDividend.Classical.avram_p4_f2_original_negative_band_nonvoid_second_order_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:10:39.329188+00:00
-- url     : https://prove2.me/theorems/604dfce2-720c-427f-b655-b2548c554962
-- title:
--   Original negative-band jump occurrence two-sided second-order probability estimate
-- statement:
--   For the original spectrally negative Lévy X, the probability of at least one negative-band jump in (0,T] differs from its physical first moment r=Tν(B) by at most r²/2: r-r²/2 ≤ P(K>0) ≤ r. Proved using exactly source count measurability, its first and factorial moments, and the Proved integral Bonferroni theorem.
-- source:
--   Imports Proved c1e09ada, 3d8bb7f8, 0a13392f, 517be7d8, f0197436 and newly published 7f0f2707. Intended source-side prebudget for Open original small-time void slope 17372d7a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_ncard_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_void_probability_factorial_integral_sandwich

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_original_negative_band_nonvoid_second_order_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    r - r ^ 2 / 2 ≤ P.real {ω : Ω | K ω ≠ 0} ∧
    P.real {ω : Ω | K ω ≠ 0} ≤ r := by sorry
