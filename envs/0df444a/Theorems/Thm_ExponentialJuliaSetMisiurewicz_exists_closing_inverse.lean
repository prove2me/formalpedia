-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_closing_inverse
-- name    : ExponentialJuliaSetMisiurewicz.exists_closing_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:34.551949+00:00
-- url     : https://prove2.me/theorems/5e2a5c7f-39f8-5411-b4ee-d21d8fdc73ba
-- title:
--   Exponential Julia Set Misiurewicz: exists closing inverse
-- statement:
--   The closing step in Lemma 6.2. A bounded branch of logarithm can be translated
--   vertically and logged again into any radius-eight disk sufficiently far to the right.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L156-L241
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean#L156-L241

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.exists_closing_inverse {D : Set ℂ} {a : ℂ} {L : ℂ → ℂ} {C : ℝ≥0}
    (hL : LipschitzOnWith C L D)
    (hclose : ∀ z ∈ D, ‖L z - L a‖ ≤ 1)
    (hinv : ∀ z ∈ D, Complex.exp (L z) = z) :
    ∃ ρ : ℝ, ∀ x : ℝ, ρ ≤ x → ∃ ψ : ℂ → ℂ,
      LipschitzOnWith C ψ D ∧ MapsTo ψ D (ball (x : ℂ) 8) ∧
      ∀ z ∈ D, expIterate 2 (ψ z) = z := by sorry
