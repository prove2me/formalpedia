-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_iterated_preimages_nonzero
-- name    : ExponentialJuliaSetMisiurewicz.dense_iterated_preimages_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:50.270741+00:00
-- url     : https://prove2.me/theorems/39a2955e-2caa-4bb1-a347-e6bb56971969
-- title:
--   Exponential Julia Set Misiurewicz: dense iterated preimages nonzero
-- statement:
--   The full iterated preimage of every nonzero point is dense in the plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L292-L297
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L292-L297

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

theorem ExponentialJuliaSetMisiurewicz.dense_iterated_preimages_nonzero {w : ℂ} (hw : w ≠ 0) :
    Dense {z : ℂ | ∃ n : ℕ, expIterate n z = w} := by sorry
