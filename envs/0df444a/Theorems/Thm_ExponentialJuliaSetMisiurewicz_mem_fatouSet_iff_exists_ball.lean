-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_mem_fatouSet_iff_exists_ball
-- name    : ExponentialJuliaSetMisiurewicz.mem_fatouSet_iff_exists_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:59.535396+00:00
-- url     : https://prove2.me/theorems/4d3de16c-9add-4445-b96d-30a2cfed53c8
-- title:
--   Exponential Julia Set Misiurewicz: mem fatou Set iff exists ball
-- statement:
--   The local Fatou-set definition can be tested on open disks.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L70-L78
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L70-L78

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.mem_fatouSet_iff_exists_ball {f : ℂ → ℂ} {z : ℂ} :
    z ∈ fatouSet f ↔ ∃ r : ℝ, 0 < r ∧
      IsNormalSequenceOn (fun n w => ((f^[n]) w : RiemannSphere)) (ball z r) := by sorry
