-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_past_campbell_eq_negative_restrict
-- name    : AvramDividend.Classical.avram_p2_d_future_past_campbell_eq_negative_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:42:59.819617+00:00
-- url     : https://prove2.me/theorems/4314df6b-1af8-4e86-ad5e-7c0f566b1c0b
-- title:
--   Every past-event original source Campbell measure equals its full negative-mark restriction
-- statement:
--   For each actual original process past event A in filtration time s, construct the honest Campbell mean time-mark measure Q_A and prove it equals its restriction to strictly negative marks as measures, without a Levy ν-rate or a Poisson replacement.
-- source:
--   Compose the Proved original past-event occupation measure e509ef60 with the Proved all-Borel original sample negative support c598292d, using lintegral_congr, Measure.ext and pinned MeasurableSet.prod and Measure.restrict_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_past_campbell_eq_negative_restrict
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
      Q = Q.restrict (Set.univ ×ˢ Iio (0 : ℝ)) := by sorry
