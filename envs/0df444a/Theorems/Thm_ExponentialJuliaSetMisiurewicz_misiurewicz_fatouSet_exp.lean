-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_misiurewicz_fatouSet_exp
-- name    : ExponentialJuliaSetMisiurewicz.misiurewicz_fatouSet_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:35.596933+00:00
-- url     : https://prove2.me/theorems/7ae8fd24-96cc-4573-bb4f-126d45d88a81
-- title:
--   Exponential Julia Set Misiurewicz: misiurewicz fatou Set exp
-- statement:
--   Misiurewicz's theorem in Fatou-set form: the sphere-valued iterates are normal
--   on no neighbourhood.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L94-L97
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L94-L97

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.misiurewicz_fatouSet_exp : fatouSet exponentialMap = ∅ := by sorry
