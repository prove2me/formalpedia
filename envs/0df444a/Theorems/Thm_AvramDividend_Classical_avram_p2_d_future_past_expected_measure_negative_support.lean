-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_past_expected_measure_negative_support
-- name    : AvramDividend.Classical.avram_p2_d_future_past_expected_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:25:05.748622+00:00
-- url     : https://prove2.me/theorems/32067a13-a60d-4675-bbf3-b16390828326
-- title:
--   Original past-restricted expected intrinsic marked measure vanishes on nonnegative mark regions
-- statement:
--   For every original past event A, construct the genuine expected source time–mark measure Q_A and establish that it gives zero mass to any jointly Borel time-mark set whose marks are nonnegative. Do not assume Q_A=dt⊗ν or any compensator identity.
-- source:
--   Combine the Proved original expected time–mark measure e509ef60 with the P2-D full-Borel source pathwise negative-support lemma c598292d once canonically Proved. The integrand is pointwise zero on C with nonnegative marks, so its restricted lintegral is zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_past_expected_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ (C : Set (ℝ≥0 × ℝ)), MeasurableSet C →
        Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)) ∧
      (∀ (C : Set (ℝ≥0 × ℝ)), MeasurableSet C →
        C ⊆ (Set.univ ×ˢ Ici (0 : ℝ)) → Q C = 0) := by sorry
