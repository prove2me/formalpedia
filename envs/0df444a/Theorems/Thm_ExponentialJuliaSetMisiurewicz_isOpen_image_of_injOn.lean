-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_image_of_injOn
-- name    : ExponentialJuliaSetMisiurewicz.isOpen_image_of_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:38.319131+00:00
-- url     : https://prove2.me/theorems/7697ad28-5a25-44ad-8c75-36b1d062c9fa
-- title:
--   Exponential Julia Set Misiurewicz: is Open image of inj On
-- statement:
--   The image of an *open set* under an injective holomorphic map is open.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L243-L264
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L243-L264

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

theorem ExponentialJuliaSetMisiurewicz.isOpen_image_of_injOn
    {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hinj : Set.InjOn g U) :
    IsOpen (g '' U) := by sorry
