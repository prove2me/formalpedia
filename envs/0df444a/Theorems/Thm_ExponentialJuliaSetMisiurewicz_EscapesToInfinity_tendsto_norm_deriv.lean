-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_EscapesToInfinity_tendsto_norm_deriv
-- name    : ExponentialJuliaSetMisiurewicz.EscapesToInfinity.tendsto_norm_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:31.618067+00:00
-- url     : https://prove2.me/theorems/4a07d2d8-2fbe-4065-8305-e1a18ef9047d
-- title:
--   Escapes To Infinity: tendsto norm deriv
-- statement:
--   **Observation 5.2, second clause.** Derivative norms tend to infinity along escaping orbits.
--   After finitely many factors, every factor in the chain rule has norm at least two.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/PaperConsequences.lean#L82-L102
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/PaperConsequences.lean#L82-L102

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_ExpChaotic_Dynamics
import Definitions.Def_ExpChaotic_PaperConsequences
set_option autoImplicit true
open Function Filter Set Metric
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.EscapesToInfinity.tendsto_norm_deriv {z : ℂ} (hz : EscapesToInfinity z) :
    Tendsto (fun n => ‖deriv (expIterate n) z‖) atTop atTop := by sorry
