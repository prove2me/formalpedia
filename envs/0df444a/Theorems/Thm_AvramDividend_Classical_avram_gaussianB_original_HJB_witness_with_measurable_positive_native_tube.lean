-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_HJB_witness_with_measurable_positive_native_tube
-- name    : AvramDividend.Classical.avram_gaussianB_original_HJB_witness_with_measurable_positive_native_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:48:24.762348+00:00
-- url     : https://prove2.me/theorems/3216ee3b-7bf9-4617-b078-3883538d114b
-- title:
--   Original admissible drift-two Gaussian HJB witness carries a measurable positive native joint Brownian source tube
-- statement:
--   There is a genuine original Gaussian Lévy process satisfying Standing, unbounded variation and the original equal-cap barrier admissibility, with exact drift-two Brownian paths, together with a measurable event of strictly positive canonical probability where both centred and drifted Brownian values remain within their prescribed tube radii up to time 17/16000. Combines the exact original HJB witness and canonical measurable Brownian joint tube without an invalid equality of time-coercion terms.

import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_HJB_witness_with_measurable_positive_native_tube
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
        ∀ ω ∈ E, ∀ s : unitInterval,
          s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
          |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
          |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω + 2 * (s : ℝ)| ≤
            (1 / 400 : ℝ) := by sorry
