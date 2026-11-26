-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_isOpen_image
-- name    : ExponentialJuliaSetMisiurewicz.lemma3_isOpen_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:36.766113+00:00
-- url     : https://prove2.me/theorems/a032162d-2f40-4be2-a684-e06eef3fa2c8
-- title:
--   Exponential Julia Set Misiurewicz: lemma3 is Open image
-- statement:
--   The image of the ball under an injective holomorphic map is open.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L267-L272
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L267-L272

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.lemma3_isOpen_image
    {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r)) :
    IsOpen (g '' ball b r) := by sorry
