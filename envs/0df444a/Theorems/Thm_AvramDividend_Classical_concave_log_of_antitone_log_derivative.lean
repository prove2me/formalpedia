-- Prove2me | Theorems.Thm_AvramDividend_Classical_concave_log_of_antitone_log_derivative
-- name    : AvramDividend.Classical.concave_log_of_antitone_log_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:21:50.026006+00:00
-- url     : https://prove2.me/theorems/97b4c7c6-e668-4b81-bb7a-26fd1f6f6cc4
-- title:
--   Log-concavity of a positive differentiable function from an antitone logarithmic derivative
-- statement:
--   For a strictly positive differentiable real function V on the positive half-line, if the logarithmic derivative V'/V is antitone, then log V is concave there. This is the analytic bridge from excursion-height tail monotonicity to the Esscher tilted scale log-concavity condition.
-- source:
--   Mathlib.Analysis.Convex.Deriv: AntitoneOn.concaveOn_of_deriv, combined with the derivative formula for the real logarithm.

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
open Set

theorem AvramDividend.Classical.concave_log_of_antitone_log_derivative
    (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x)
    (hanti : AntitoneOn (fun x : ℝ => deriv V x / V x) (Set.Ioi (0 : ℝ))) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by sorry
