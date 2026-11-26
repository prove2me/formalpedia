-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_exists_im_far_apart_two_pi
-- name    : ExponentialJuliaSetMisiurewicz.lemma4_exists_im_far_apart_two_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:50.929586+00:00
-- url     : https://prove2.me/theorems/e5435026-6d9c-5838-8974-45509e850142
-- title:
--   Exponential Julia Set Misiurewicz: lemma4 exists im far apart two pi
-- statement:
--   If infinitely many images miss the central strip, some image has imaginary diameter
--   at least `2π`. If every iterate is injective, derivative growth and Lemma 3 produce a
--   large image disk. Otherwise, the first failure of injectivity gives a pair separated
--   by a nonzero period of the exponential.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L120-L239
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/StripGeometry.lean#L120-L239

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

theorem ExponentialJuliaSetMisiurewicz.lemma4_exists_im_far_apart_two_pi
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinf : {n : ℕ | Disjoint (expIterate n '' V) centralStrip}.Infinite) :
    ∃ (n : ℕ) (w z : ℂ), w ∈ V ∧ z ∈ V ∧
      2 * Real.pi ≤ |(expIterate n w).im - (expIterate n z).im| := by sorry
