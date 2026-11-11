-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_compound_driver_to_original_source
-- name    : AvramDividend.Classical.avram_a06_bv_compound_driver_to_original_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T17:03:54.602196+00:00
-- url     : https://prove2.me/theorems/fbe058fd-962c-4ce9-ae88-5ce95cba3ed3
-- title:
--   Construct the filtered original BV spectrally negative Levy process from its compound-Poisson driver
-- statement:
--   Given the exact pair-of-real-sequences sample space with a jointly independent unit-rate compound-Poisson driver and uniform negative marks, construct the original spectrally negative Levy record using its natural filtration. Prove pathwise càdlàg and downward-jump properties via a full-measure gate, independent stationary increments, correct Laplace moments and triplet, positive drift, finite first moment and bounded variation. This is the sole genuine stochastic adapter needed to assemble the A06 counterexample source.
-- source:
--   Parent 115c3b1e is the selected source child for A06 disproof sketch 3281148e. Public Proved driver 726c336d, published product driver 868ae26c, mark facts 4f8f174b and BV moments 51e4a4b3 provide the explicit inputs. The remaining obligation is the original filtered process construction and its exact Avram Laplace law, rather than an unidentified auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_compound_driver_to_original_source
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.BoundedVariation ∧
        X.ν (Iio (0 : ℝ)) < ⊤ ∧
        0 < X.drift ∧
        X.ν ≠ 0 ∧
        Integrable (X.X 1) P ∧
        X.ν ≪ volume := by sorry
