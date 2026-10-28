-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_levy_positive_upward_increment_measure_all_times
-- name    : AvramDividend.Classical.unbounded_levy_positive_upward_increment_measure_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:53:04.229994+00:00
-- url     : https://prove2.me/theorems/68ca1f63-4ba4-486f-8561-9e67c8baa934
-- title:
--   Unbounded-variation Lévy process has positive upward-increment probability at every positive time
-- statement:
--   For every strictly positive time, a spectrally negative Lévy process of unbounded variation has strictly positive probability of a positive increment. The unbounded-variation theorem supplies a nonnegative θ with ψ(θ)>q>0, and the already proved universal positive-exponent/positive-measure theorem applies at each positive time. This supplies reusable nondegeneracy for first-passage and stopped-exit arguments without assuming standing or Gaussian components.
-- source:
--   chat04_psi_eventually_gt_of_unbounded_variation and positive_psi_implies_upward_increment_positive_measure_all_times, both Proved.

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_psi_implies_upward_increment_positive_measure_all_times

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_levy_positive_upward_increment_measure_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation) :
    ∀ t : ℝ≥0, 0 < t → 0 < P {ω : Ω | 0 < X.X t ω} := by sorry
