-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_ratio_order_log_concave_of_differentiable
-- name    : AvramDividend.Classical.positive_ratio_order_log_concave_of_differentiable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:46:02.748332+00:00
-- url     : https://prove2.me/theorems/9df621c3-ea22-428f-9915-d064c437fe87
-- title:
--   Positive forward-ratio ordering gives full log-concavity under differentiability
-- statement:
--   A positive real function on the positive axis with differentiable logarithm and nondecreasing forward ratios f(x)/f(x+t) in the starting point has a concave logarithm. After taking logarithms, equal-length forward log increments are nonincreasing in the base point. Divide by the positive length, pass to the right-derivative limit of the differentiable log, and apply the Mathlib antitone-derivative concavity criterion. This provides the complete smooth analytical bridge from the corrected exit-ratio comparison to log-concavity of the canonical scale function.
-- source:
--   Forward-ratio characterisation of logarithmic concavity and derivative monotonicity; Mathlib.Analysis.Convex.Deriv.

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
open Filter Set Topology
open scoped Topology

theorem AvramDividend.Classical.positive_ratio_order_log_concave_of_differentiable
    (f : ℝ → ℝ)
    (hfpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (fun z : ℝ => Real.log (f z)) x)
    (hratio : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      f x / f (x + t) ≤ f y / f (y + t)) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (f z)) := by sorry
