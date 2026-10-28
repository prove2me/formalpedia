-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_path_residual_monotone_of_increment_bounds
-- name    : AvramDividend.Classical.bv_path_residual_monotone_of_increment_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:16:39.990576+00:00
-- url     : https://prove2.me/theorems/d547df26-89cf-4347-9362-be648cc16803
-- title:
--   Drift-bounded increments imply monotone residual path
-- statement:
--   A deterministic pathwise implication: if every ordered Lévy-process increment is bounded above by the linear drift over its time increment, then the residual process t·drift−X_t is nondecreasing. This isolates the final algebra of the subordinator path argument.
-- source:
--   Avram Palmowski Pistorius (2007), finite-activity bounded-variation process-law foundations; already-Proved increment support lemma.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_path_residual_monotone_of_increment_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω)
    (hinc : ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω ≤ ((t - s : ℝ≥0) : ℝ) * X.drift) :
    Monotone (fun t : ℝ≥0 => (t : ℝ) * X.drift - X.X t ω) := by sorry
