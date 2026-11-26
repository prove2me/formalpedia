-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_int_mul_pi
-- name    : ExponentialJuliaSetMisiurewicz.lemma4_exists_im_int_mul_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:35.01204+00:00
-- url     : https://prove2.me/theorems/29053817-2607-410a-a6d0-9dd6ebbd89b8
-- title:
--   Exponential Julia Set Misiurewicz: lemma4 exists im int mul pi
-- statement:
--   From two far-apart imaginary parts, the intermediate value theorem on the connected set
--   `V` produces a point whose imaginary part is an exact integer multiple of `π`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L316-L359
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L316-L359

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

theorem ExponentialJuliaSetMisiurewicz.lemma4_exists_im_int_mul_pi
    {V : Set ℂ} (hVconn : IsConnected V)
    (h : ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      Real.pi ≤ |(expIterate n w).im - (expIterate n z).im|) :
    ∃ (n : ℕ) (y : ℂ) (k : ℤ), y ∈ V ∧ (expIterate n y).im = k * Real.pi := by sorry
