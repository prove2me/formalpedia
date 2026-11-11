-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_stationary_increments_add_linear_drift
-- name    : AvramDividend.Classical.avram_a06_stationary_increments_add_linear_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:38:19.783497+00:00
-- url     : https://prove2.me/theorems/aa7fdc4f-5b8c-43cf-bc39-657996cc0668
-- title:
--   Adding deterministic linear drift preserves stationary increments
-- statement:
--   For any original-space real stochastic process with stationary increments, adding a deterministic linear drift preserves that increment property. This isolates the straightforward deterministic transfer needed after the marked-renewal zero-drift source is established.
-- source:
--   LeanLevy stochastic process increment definitions; deterministic translation invariance of equal distributions and independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_stationary_increments_add_linear_drift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (hZ : HasStationaryIncrements Z P) :
    HasStationaryIncrements (fun t ω => Z t ω + b * (t : ℝ)) P := by sorry
