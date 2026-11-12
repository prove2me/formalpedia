-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_zero_drift_marked_stationary
-- name    : AvramDividend.Classical.avram_a06_original_zero_drift_marked_stationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:33:42.84789+00:00
-- url     : https://prove2.me/theorems/2dafc572-bbad-46ff-8d7c-825c3eb0ded8
-- title:
--   Original marked-renewal jump sum has stationary increments
-- statement:
--   The zero-drift, same-space marked renewal jump-sum process built from the original exponential interarrivals and uniform negative independent marks has stationary increments. This is the exact stochastic marked-band law needed with the deterministic finite-sum increment identity to establish the raw compound-Poisson increment theorem.
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

theorem AvramDividend.Classical.avram_a06_original_zero_drift_marked_stationary
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    HasStationaryIncrements
      (fun (t : ℝ≥0) ω =>
        LevyFoundations.piecewisePath 0 0
          (fun n => LevyFoundations.arrival τ n ω)
          (fun n => Y n ω) (t : ℝ)) P := by sorry
