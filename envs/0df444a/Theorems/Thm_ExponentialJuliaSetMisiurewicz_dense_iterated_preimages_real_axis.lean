-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_iterated_preimages_real_axis
-- name    : ExponentialJuliaSetMisiurewicz.dense_iterated_preimages_real_axis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:51.771807+00:00
-- url     : https://prove2.me/theorems/11648038-55b5-518f-bb24-2465f4e6d7c0
-- title:
--   Exponential Julia Set Misiurewicz: dense iterated preimages real axis
-- statement:
--   The backward orbit of the real axis is dense.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L300-L304
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L300-L304

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.dense_iterated_preimages_real_axis :
    Dense {z : ℂ | ∃ n : ℕ, OnRealAxis (expIterate n z)} := by sorry
