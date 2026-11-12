-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_gated_stationary_increments
-- name    : AvramDividend.Classical.avram_a06_original_compound_gated_stationary_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:41:49.656977+00:00
-- url     : https://prove2.me/theorems/e32abfbc-2c4d-4933-8e2b-f6b5f76a39ef
-- title:
--   Original marked compound-Poisson full-measure gate has stationary increments
-- statement:
--   Prove stationary increment laws on the original marked-compound-Poisson probability space. The measurable full-measure gate makes only a null-set modification. This is an indispensable component of the full IsLevyProcess certificate.
-- source:
--   A06 corrected original-space source, genuine stochastic increment laws.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compound_gated_stationary_increments
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (G : Set ((ℕ → ℝ) × (ℕ → ℝ)))
    [DecidablePred (fun ω => ω ∈ G)]
    (hGmeas : MeasurableSet G) (hGae : ∀ᵐ ω ∂P, ω ∈ G) :
    HasStationaryIncrements
      (fun (t : ℝ≥0) ω =>
        if ω ∈ G then LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω
        else (0 : ℝ)) P := by sorry
