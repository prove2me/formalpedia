-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_independent_increments_add_linear_drift
-- name    : AvramDividend.Classical.avram_a06_independent_increments_add_linear_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:38:21.933103+00:00
-- url     : https://prove2.me/theorems/bd4903a9-0c04-4533-9c96-f7c6f898a9e0
-- title:
--   Adding deterministic linear drift preserves independent increments
-- statement:
--   For any original-space real stochastic process with independent increments, adding a deterministic linear drift preserves that increment property. This isolates the straightforward deterministic transfer needed after the marked-renewal zero-drift source is established.
-- source:
--   LeanLevy stochastic process increment definitions; deterministic translation invariance of equal distributions and independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_independent_increments_add_linear_drift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (hZ : HasIndependentIncrements Z P) :
    HasIndependentIncrements (fun t ω => Z t ω + b * (t : ℝ)) P := by sorry
