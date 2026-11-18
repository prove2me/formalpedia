-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_admissible_positive_event_actual_floor_clock
-- name    : AvramDividend.Classical.avram_gaussianB_original_admissible_positive_event_actual_floor_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:56:09.969193+00:00
-- url     : https://prove2.me/theorems/436fd893-39f5-4c97-b3d6-a5c9d440f69d
-- title:
--   On a measurable positive-probability original Gaussian event the actual pre-ruin floor stopping clock equals the strictly positive horizon
-- statement:
--   An actual original HJB-admissible drift-two Gaussian Lévy model admits a measurable event of strictly positive canonical probability on which the true original cap-barrier reserve stays above the upper fixed-band cutoff 5/44 up to T=1/1000. The original clipped floor stopping clock formed by the first reserve hitting 5/44 is exactly T and hence positive on the event, and the terminal reserve lies between 5/44 and C=1/8. This combines Proved B51 geometry with a genuine canonical Brownian small-ball event and is a key stopped-clock condition for refuting the flawed fixed-j Gaussian cash inequality.

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_canonical_measurable_positive_joint_long_tube
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_admissible_positive_event_actual_floor_clock
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
        ∀ ω ∈ E,
          sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
          (fun t : ℝ≥0 => -(riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
            Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)}) = (1 / 1000 : ℝ≥0) ∧
          (5 / 44 : ℝ) < riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω ∧
          riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω ≤ (1 / 8 : ℝ) := by sorry
