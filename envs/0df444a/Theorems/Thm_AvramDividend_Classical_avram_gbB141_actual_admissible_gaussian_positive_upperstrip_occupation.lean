-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB141_actual_admissible_gaussian_positive_upperstrip_occupation
-- name    : AvramDividend.Classical.avram_gbB141_actual_admissible_gaussian_positive_upperstrip_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:56:13.437719+00:00
-- url     : https://prove2.me/theorems/f2becb33-a7d9-4582-93ad-337fb675b09f
-- title:
--   Concrete admissible original Gaussian source has strictly positive omitted upper-cap occupation on short tube
-- statement:
--   There exists an original admissible HJB Gaussian Lévy model with standing assumptions, unbounded variation and exact Brownian drift-two paths, such that on every narrow positive Gaussian source tube the upper-cap strip occupation appearing in the corrected cash bound is strictly positive. This is source-faithful evidence that the positive-drift occupation term cannot be dropped by a purely pointwise zero estimate; event positivity and the stochastic cash ledger remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_exact_gaussian_tube_positive_fixed_band_occupation
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB141_actual_admissible_gaussian_positive_upperstrip_occupation :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      (∀ ω : ℝ≥0 → ℝ,
        (∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
          |Y.X s ω| ≤ (1 / 400 : ℝ)) →
        0 < ∫ t in Ioo (0 : ℝ) (1 : ℝ),
          if t < (1 / 1000 : ℝ) ∧
              (5 / 44 : ℝ) <
                riskProcess Y (1 / 8 : ℝ)
                  (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ))
                  (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume) := by sorry
