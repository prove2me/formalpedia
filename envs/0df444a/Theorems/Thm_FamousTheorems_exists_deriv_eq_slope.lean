-- Prove2me | Theorems.Thm_FamousTheorems_exists_deriv_eq_slope
-- name    : FamousTheorems.exists_deriv_eq_slope
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:29.402719+00:00
-- url     : https://prove2.me/theorems/0a07eeee-52d3-4e94-8beb-320ce95a3601
-- title:
--   The mean value theorem
-- statement:
--   **Lagrange's mean value theorem.**
--
--   For $f$ continuous on $[a,b]$ and differentiable on $(a,b)$, there is $c \in (a,b)$ with
--   $$f'(c) \;=\; \frac{f(b)-f(a)}{b-a}.$$
--
--   Some instantaneous rate of change equals the average rate. It follows from Rolle's theorem
--   applied to $f$ minus the secant line, and Rolle in turn from the extreme value theorem.
--
--   It is the workhorse that converts derivative information into function information: that
--   $f' = 0$ implies $f$ constant, that $f' > 0$ implies strictly increasing, the error term in
--   Taylor's theorem, and L'Hôpital's rule all reduce to it. Differentiability is needed only on
--   the open interval, which is what lets it apply to functions like $\sqrt{x}$ on $[0,1]$.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem exists_deriv_eq_slope : ∀ (f : ℝ → ℝ) {a b : ℝ}, a < b →
    ContinuousOn f (Set.Icc a b) → DifferentiableOn ℝ f (Set.Ioo a b) →
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) := by sorry

end FamousTheorems
