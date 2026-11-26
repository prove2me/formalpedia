-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_IsNormalSequenceOn_mono
-- name    : ExponentialJuliaSetMisiurewicz.IsNormalSequenceOn.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:32.821885+00:00
-- url     : https://prove2.me/theorems/6e9e2121-a557-45a1-aa1e-e9d773050bb9
-- title:
--   Is Normal Sequence On: mono
-- statement:
--   Normality is inherited by subsets. A limit on `U` restricts along the continuous
--   inclusion `V → U`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L60-L67
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L60-L67

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.IsNormalSequenceOn.mono {α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ℕ → α → β} {U V : Set α} (h : IsNormalSequenceOn F U) (hVU : V ⊆ U) :
    IsNormalSequenceOn F V := by sorry
