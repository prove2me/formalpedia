-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compoundPoisson_filtered_law_core
-- name    : AvramDividend.Classical.avram_a06_original_compoundPoisson_filtered_law_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:24:13.778998+00:00
-- url     : https://prove2.me/theorems/b1eb5fe7-30d3-452d-9980-58cfa274b47d
-- title:
--   Original filtered Lévy process realises the compound-Poisson law at all fixed times
-- statement:
--   For the genuine independent uniform-mark compound-Poisson driver on the exact product sample space, construct a pathwise cadlag no-positive-jump spectrally negative Lévy process with a natural adapted filtration, independent stationary increments and compensated Laplace triplet, such that every deterministic-time marginal is almost surely the original compoundPoisson path. The first-moment field is deliberately kept in the parent constructor, already addressed by separate source-exact integrability lemmas.
-- source:
--   Only still-hard stochastic and Laplace portion of Open fd251b85 after independently proving first moments through the Poisson jump-count envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compoundPoisson_filtered_law_core
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
          (∫ y in Ioo (-1 : ℝ) 0,
            y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) ∧
        (∀ t : ℝ≥0,
          X.X t =ᵐ[P] LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ)) := by sorry
