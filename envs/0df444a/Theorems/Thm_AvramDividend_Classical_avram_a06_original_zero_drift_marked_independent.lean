-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_zero_drift_marked_independent
-- name    : AvramDividend.Classical.avram_a06_original_zero_drift_marked_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:33:39.242685+00:00
-- url     : https://prove2.me/theorems/6a70907a-98c6-452c-8455-d4b63d0aa546
-- title:
--   Original marked-renewal jump sum has independent increments
-- statement:
--   The zero-drift, same-space marked renewal jump-sum process built from the original exponential interarrivals and uniform negative independent marks has independent increments. This is the exact stochastic marked-band law needed with the deterministic finite-sum increment identity to establish the raw compound-Poisson increment theorem.
-- source:
--   Original Lévy compound Poisson marked renewal construction; IsCompoundPoissonDriver joint i.i.d. exponential interarrivals and marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_zero_drift_marked_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    HasIndependentIncrements
      (fun (t : ℝ≥0) ω =>
        LevyFoundations.piecewisePath 0 0
          (fun n => LevyFoundations.arrival τ n ω)
          (fun n => Y n ω) (t : ℝ)) P := by sorry
