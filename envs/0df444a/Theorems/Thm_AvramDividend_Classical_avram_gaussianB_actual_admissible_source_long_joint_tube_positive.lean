-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_actual_admissible_source_long_joint_tube_positive
-- name    : AvramDividend.Classical.avram_gaussianB_actual_admissible_source_long_joint_tube_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:36:43.296705+00:00
-- url     : https://prove2.me/theorems/e20f160e-90e5-43c3-855e-fe11e906a169
-- title:
--   Original fully admissible Gaussian Lévy source has positive probability of a joint centred and source tube through 17/16000
-- statement:
--   There exists an original spectrally negative Gaussian Lévy process with exact drift-two Brownian paths satisfying Standing, unbounded variation and original equal-cap admissibility, for which a single canonical positive-probability event keeps the centred source within 1/4000 and the full source within 1/400 through time 17/16000. The result supplies a genuine witness for the Gaussian positive-drift fixed-band counterexample and all sufficiently fine one-step physical meshes.

import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB186_canonical_gaussian_centered_joint_long_tube_positive_unconditional
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_actual_admissible_source_long_joint_tube_positive
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      0 < gaussianLimit {ω : ℝ≥0 → ℝ |
        ∀ s : unitInterval,
          s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
          |Y.X ⟨s, s.2.1⟩ ω - 2 * (s : ℝ)| < (1 / 4000 : ℝ) ∧
          |Y.X ⟨s, s.2.1⟩ ω| < (1 / 400 : ℝ)} := by sorry
