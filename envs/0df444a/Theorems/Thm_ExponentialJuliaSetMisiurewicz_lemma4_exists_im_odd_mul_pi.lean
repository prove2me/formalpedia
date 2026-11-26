-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_odd_mul_pi
-- name    : ExponentialJuliaSetMisiurewicz.lemma4_exists_im_odd_mul_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:26.059802+00:00
-- url     : https://prove2.me/theorems/9a3124f5-2b17-5da6-979e-97d5834c4ecf
-- title:
--   Exponential Julia Set Misiurewicz: lemma4 exists im odd mul pi
-- statement:
--   With an imaginary spread of `2π`, the intermediate value theorem finds a point whose
--   imaginary part is an *odd* multiple of `π`: the interval contains two consecutive multiples,
--   and one of them is odd.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L254-L298
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L254-L298

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

theorem ExponentialJuliaSetMisiurewicz.lemma4_exists_im_odd_mul_pi
    {V : Set ℂ} (hVconn : IsConnected V)
    (h : ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      2 * Real.pi ≤ |(expIterate n w).im - (expIterate n z).im|) :
    ∃ (n : ℕ) (y : ℂ) (k : ℤ),
      y ∈ V ∧ Odd k ∧ (expIterate n y).im = (k : ℝ) * Real.pi := by sorry
