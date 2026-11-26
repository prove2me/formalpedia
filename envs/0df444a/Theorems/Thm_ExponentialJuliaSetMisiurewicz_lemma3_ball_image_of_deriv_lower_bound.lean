-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_ball_image_of_deriv_lower_bound
-- name    : ExponentialJuliaSetMisiurewicz.lemma3_ball_image_of_deriv_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:33.027808+00:00
-- url     : https://prove2.me/theorems/7c62f016-f585-5786-90bf-1df7415b5c35
-- title:
--   Exponential Julia Set Misiurewicz: lemma3 ball image of deriv lower bound
-- statement:
--   **Lemma 3.** Quantitative open mapping estimate, following Harrison's `LEMMA_3`.
--   The proof uses his closest-point device: `t` is the distance from `g b` to the complement of
--   the image, so `ball (g b) t` lies in the image and is convex, which is exactly what the mean
--   value inequality needs.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L319-L435
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean#L319-L435

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

theorem ExponentialJuliaSetMisiurewicz.lemma3_ball_image_of_deriv_lower_bound
    {g : ℂ → ℂ} {b : ℂ} {r m : ℝ}
    (hr : 0 < r) (hm : 0 ≤ m)
    (hgc : ContinuousOn g (closedBall b r))
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r))
    (hderiv : ∀ z ∈ ball b r, m ≤ ‖deriv g z‖) :
    ball (g b) (r * m) ⊆ g '' ball b r := by sorry
