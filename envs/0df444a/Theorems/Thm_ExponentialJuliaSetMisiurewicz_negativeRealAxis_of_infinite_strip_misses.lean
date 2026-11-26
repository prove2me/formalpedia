-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_negativeRealAxis_of_infinite_strip_misses
-- name    : ExponentialJuliaSetMisiurewicz.negativeRealAxis_of_infinite_strip_misses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:05:05.525981+00:00
-- url     : https://prove2.me/theorems/1da7aa17-ac2f-4e37-b400-f8e8f75b86bf
-- title:
--   Exponential Julia Set Misiurewicz: negative Real Axis of infinite strip misses
-- statement:
--   **Negative-axis strengthening, conditional form.** If infinitely many forward images of
--   `V` avoid the central strip, then some forward image meets the *negative* real axis.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L302-L312
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L302-L312

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.negativeRealAxis_of_infinite_strip_misses
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    EventuallyMeetsNegativeRealAxis V := by sorry
