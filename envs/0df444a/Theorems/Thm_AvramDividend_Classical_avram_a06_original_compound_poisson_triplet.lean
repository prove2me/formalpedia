-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_poisson_triplet
-- name    : AvramDividend.Classical.avram_a06_original_compound_poisson_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:32:10.734404+00:00
-- url     : https://prove2.me/theorems/fd251b85-ff0c-4b9b-873e-e92b8dec2f64
-- title:
--   Construct the source-exact original filtered compound-Poisson Avram Lévy triplet
-- statement:
--   From a genuine unit-rate compound-Poisson driver with compact negative uniform marks on the exact fixed product sample space, construct a filtered SpectrallyNegativeLevy whose Gaussian coefficient vanishes, Lévy measure is the given negative mark law, c is physical drift one plus its small-jump mean, and first moment is integrable. The record must justify all-path càdlàg downward jumps, adaptedness, independent stationary increments and the exponential Laplace identity.
-- source:
--   Genuine stochastic portion of Open adapter fbe058fd. Exact source definition of drift is L.c minus the small-jump mean. Separate Proved measure and BV lemmas discharge all remaining source predicates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory AvramDividend.Classical Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_poisson_triplet
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.σ = 0 ∧
        X.ν = ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) ∧
        X.c = (1 : ℝ) +
          (∫ y in Ioo (-1 : ℝ) 0, y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) ∧
        Integrable (X.X 1) P := by sorry
