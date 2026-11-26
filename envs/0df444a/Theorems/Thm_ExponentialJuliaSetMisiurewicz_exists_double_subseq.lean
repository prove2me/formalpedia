-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_double_subseq
-- name    : ExponentialJuliaSetMisiurewicz.exists_double_subseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:47.308828+00:00
-- url     : https://prove2.me/theorems/50af5433-286f-4d2c-94bb-58e7211c3fc3
-- title:
--   Exponential Julia Set Misiurewicz: exists double subseq
-- statement:
--   Two sequences in compact sets admit a *common* convergent subsequence.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L73-L83
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/RealAxis.lean#L73-L83

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.exists_double_subseq {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s : Set X} {t : Set Y} (hs : IsCompact s) (ht : IsCompact t)
    {a : ℕ → X} {b : ℕ → Y} (ha : ∀ n, a n ∈ s) (hb : ∀ n, b n ∈ t) :
    ∃ x ∈ s, ∃ y ∈ t, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (a ∘ φ) Filter.atTop (𝓝 x) ∧
      Filter.Tendsto (b ∘ φ) Filter.atTop (𝓝 y) := by sorry
