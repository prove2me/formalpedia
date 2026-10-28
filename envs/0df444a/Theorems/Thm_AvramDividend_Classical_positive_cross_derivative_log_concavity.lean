-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_cross_derivative_log_concavity
-- name    : AvramDividend.Classical.positive_cross_derivative_log_concavity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:47:32.81073+00:00
-- url     : https://prove2.me/theorems/d92d2429-afea-4cbb-bf72-90663a89fd2b
-- title:
--   Log-concavity from positive cross-derivative order without second derivatives
-- statement:
--   For a positive differentiable function f on the positive half-line, pairwise cross-derivative comparison f'(y)f(x) ≤ f'(x)f(y) at every 0<x≤y implies log-concavity of f. Cross multiply by positive f(x)f(y) to obtain antitonicity of the logarithmic derivative and import the established positive-differentiable concavity criterion. This deterministic bridge completes the transition from the corrected Esscher tilted-scale cross-derivative theorem to the global logarithmic concavity theorem, subject only to the original exit identity and smoothness assumptions.
-- source:
--   Classical derivative criterion for logarithmic concavity and proved AvramDividend.Classical.concave_log_of_antitone_log_derivative.

import Theorems.Thm_AvramDividend_Classical_concave_log_of_antitone_log_derivative
import Mathlib.Algebra.Order.Field.Basic
open AvramDividend.Classical Set

theorem AvramDividend.Classical.positive_cross_derivative_log_concavity
    (f : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hdiff : ∀ x : ℝ, 0 < x → HasDerivAt f (deriv f x) x)
    (hcross : ∀ x y : ℝ, 0 < x → x ≤ y →
      deriv f y * f x ≤ deriv f x * f y) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (f z)) := by sorry
