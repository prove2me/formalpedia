-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_cap_barrier_has_strictly_positive_omitted_drift_occupation_on_tube
-- name    : AvramDividend.Classical.avram_gaussianB_original_cap_barrier_has_strictly_positive_omitted_drift_occupation_on_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:13:48.522786+00:00
-- url     : https://prove2.me/theorems/7cabcce8-be52-454c-91f6-05062b1cf9ff
-- title:
--   Actual admissible original Gaussian barrier carries a strictly positive missing drift occupation term on every small source tube
-- statement:
--   For every positive horizon T, the actual drift-two Gaussian spectrally negative Lévy process and admissible equal-cap barrier of the Proved B51 source satisfy that on any path whose source remains within the 1/400 tube, the positive drift occupation integral above the barrier b=5/44 is strictly positive. This explicitly documents the term missing in the original positive-drift fixed-j stochastic cash inequality.

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_cap_barrier_has_strictly_positive_omitted_drift_occupation_on_tube
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      (∀ ω : ℝ≥0 → ℝ,
        (∀ s : ℝ≥0, s ≤ T → |Y.X s ω| ≤ (1 / 400 : ℝ)) →
        0 < (2 : ℝ) * ∫ t in Ioo (0 : ℝ) (T : ℝ),
          (if (5 / 44 : ℝ) <
              riskProcess Y (1 / 8 : ℝ)
                (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                (Real.toNNReal t) ω
            then (1 : ℝ) else 0) ∂volume) := by sorry
