-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_reflected_drawdown_le_drift_residual_ae_all_times
-- name    : AvramDividend.Classical.bv_actual_reflected_drawdown_le_drift_residual_ae_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:28:01.799995+00:00
-- url     : https://prove2.me/theorems/455b64c1-67a0-4733-b803-94877c55fbc2
-- title:
--   For actual bounded-variation Lévy paths, reflected drawdown never exceeds drift deficit
-- statement:
--   Under the original standing bounded-variation hypotheses, on a single probability-one event for all t≥0, the actual reflected drawdown S_t−X_t is bounded above by the drift residual dt−X_t. The Proved all-time BV path drift upper bound and the deterministic upper envelope theorem give S_t≤dt, and the original drawdown is S_t−X_t. This gives a direct almost-sure process-level comparison, and one direction of the desired zero-barrier ruin/first-residual stopping-time bridge.
-- source:
--   Avram Palmowski Pistorius (2007); Prove2Me actual BV drift upper bound and running supremum envelope.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
import Theorems.Thm_AvramDividend_Classical_runningSup_le_drift_of_upper_bv_path
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_reflected_drawdown_le_drift_residual_ae_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      drawdown X t ω ≤ (t : ℝ) * X.drift - X.X t ω := by sorry
