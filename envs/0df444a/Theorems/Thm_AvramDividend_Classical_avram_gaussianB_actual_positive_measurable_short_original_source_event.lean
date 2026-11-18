-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_actual_positive_measurable_short_original_source_event
-- name    : AvramDividend.Classical.avram_gaussianB_actual_positive_measurable_short_original_source_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:55:10.015503+00:00
-- url     : https://prove2.me/theorems/2160d763-2352-449e-bc22-70d1b864efe7
-- title:
--   Fully admissible original drift-two Gaussian source has a measurable positive-probability short stopped-cash contradiction event
-- statement:
--   There is an exact original drift-two Brownian Lévy source satisfying Standing, unbounded variation and equal-cap admissibility and a measurable canonical Gaussian event with strictly positive probability such that every original source time t≤1/1000 satisfies the drift-two path representation, centred Brownian radius 1/4000 and original source radius 1/400. These are precisely the source and event premises of the Proved B180 original stopped cash contradiction, eliminating reliance on a surrogate Brownian model.

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_with_measurable_positive_native_joint_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_actual_positive_measurable_short_original_source_event
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        (∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
          Y.X t ω = (brownian t ω - brownian 0 ω) +
            2 * (t : ℝ) ∧
          |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
          |Y.X t ω| ≤ (1 / 400 : ℝ)) := by sorry
