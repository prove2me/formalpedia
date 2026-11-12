-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_stationary
-- name    : AvramDividend.Classical.avram_a06_original_marked_band_stationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:55:45.528757+00:00
-- url     : https://prove2.me/theorems/58bedce7-0037-4f61-a49f-000796265496
-- title:
--   Original exponential-renewal marked arrival-band sums have stationary distributions
-- statement:
--   The exact finite mark sum between original exponential-renewal arrival counts over [s,s+k] has the same probability distribution as the mark sum over [0,k]. This is the source-specific renewal-memorylessness theorem needed for stationary increments of the original compound-Poisson path.
-- source:
--   Original driver has jointly independent Exp(1) interarrivals and uniform negative marks; marked Poisson renewal memorylessness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_marked_band_stationary
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.Ico (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (s : ℝ)) (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)), Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ)) (LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) (k : ℝ)), Y j ω)
      P P := by sorry
