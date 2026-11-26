-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact
-- name    : ExponentialJuliaSetMisiurewicz.eventually_covers_compact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:31.273819+00:00
-- url     : https://prove2.me/theorems/a73ea9ca-9bd9-4e9f-8cb7-fc7dfee25165
-- title:
--   Exponential Julia Set Misiurewicz: eventually covers compact
-- statement:
--   **Corollary 5.5 (open sets spread everywhere).** Every sufficiently late
--   iterated image of a nonempty open set contains any given compact set omitting zero.
--   Only real-axis Lemma 6 and the quantitative open-mapping Lemma 3 are needed.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L228-L256
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean#L228-L256

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

theorem ExponentialJuliaSetMisiurewicz.eventually_covers_compact
    {U K : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' U := by sorry
