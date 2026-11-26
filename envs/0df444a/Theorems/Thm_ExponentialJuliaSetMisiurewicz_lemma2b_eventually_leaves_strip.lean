-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma2b_eventually_leaves_strip
-- name    : ExponentialJuliaSetMisiurewicz.lemma2b_eventually_leaves_strip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:35.976023+00:00
-- url     : https://prove2.me/theorems/6e1ec1da-30a3-46d2-9501-967ff8cb4622
-- title:
--   Exponential Julia Set Misiurewicz: lemma2b eventually leaves strip
-- statement:
--   **Lemma 2(b).** Every non-real orbit eventually leaves the central strip.
--   HOL Light: `LEMMA_2b`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L145-L240
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L145-L240

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

theorem ExponentialJuliaSetMisiurewicz.lemma2b_eventually_leaves_strip {z : ℂ} (hz : ¬ OnRealAxis z) :
    ∃ n : ℕ, expIterate n z ∉ centralStrip := by sorry
