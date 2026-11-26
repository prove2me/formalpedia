-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_far_apart
-- name    : ExponentialJuliaSetMisiurewicz.lemma4_exists_im_far_apart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:24.859502+00:00
-- url     : https://prove2.me/theorems/7d505caf-d533-5baa-a2b3-8d2e4cf70cc1
-- title:
--   Exponential Julia Set Misiurewicz: lemma4 exists im far apart
-- statement:
--   Some forward image of `V` contains two points whose imaginary parts differ by at least `π`,
--   given that infinitely many forward images avoid the central strip.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L243-L249
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L243-L249

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

theorem ExponentialJuliaSetMisiurewicz.lemma4_exists_im_far_apart
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      Real.pi ≤ |(expIterate n w).im - (expIterate n z).im| := by sorry
