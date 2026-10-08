-- Prove2me | Theorems.Thm_AvramDividend_Classical_log_derivative_antitone_of_concave_log
-- name    : AvramDividend.Classical.log_derivative_antitone_of_concave_log
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:21:05.115277+00:00
-- url     : https://prove2.me/theorems/3fdd1623-196b-4d94-b992-ab86c675f0e6
-- title:
--   Concavity of log V forces its logarithmic derivative to be antitone
-- statement:
--   For a positive differentiable real function V on (0,infinity), if log V is concave there and V'(x)=V(x)g(x), then g is the derivative of log V and is nonincreasing. This generic derivative monotonicity lemma is a reusable substep of the analytic alternative to the Lévy excursion-height formula; proving log-concavity of the tilted scale function itself is a separate nontrivial stochastic problem.
-- source:
--   Pinned Mathlib ConcaveOn.antitoneOn_deriv and HasDerivAt.log.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped Topology

theorem AvramDividend.Classical.log_derivative_antitone_of_concave_log
    (V g : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hlogconcave :
      ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x) :
    AntitoneOn g (Ioi (0 : ℝ)) := by sorry
