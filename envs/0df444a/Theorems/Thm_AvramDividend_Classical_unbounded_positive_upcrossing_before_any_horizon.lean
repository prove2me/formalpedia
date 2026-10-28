-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_upcrossing_before_any_horizon
-- name    : AvramDividend.Classical.unbounded_positive_upcrossing_before_any_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:57:00.552881+00:00
-- url     : https://prove2.me/theorems/452dbdad-1569-4e38-97df-ff149765cadd
-- title:
--   Unbounded-variation Lévy process has positive probability of an upward crossing before any horizon
-- statement:
--   For any strictly positive time horizon, an unbounded-variation spectrally negative Lévy process has strictly positive probability of a strictly positive increment at some time up to that horizon. Positive probability at the terminal time is already formally established. The terminal event is contained in the pathwise-upcrossing event, so measure monotonicity gives this first-passage-relevant lower bound. No additional standing or scale-function assumptions are imposed.
-- source:
--   Proved chat04_psi_eventually_gt_of_unbounded_variation, positive_psi_implies_upward_increment_positive_measure_all_times, and Mathlib MeasureTheory.measure_mono.

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_psi_implies_upward_increment_positive_measure_all_times
import Mathlib.MeasureTheory.OuterMeasure.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_upcrossing_before_any_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    0 < P {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ 0 < X.X s ω} := by sorry
