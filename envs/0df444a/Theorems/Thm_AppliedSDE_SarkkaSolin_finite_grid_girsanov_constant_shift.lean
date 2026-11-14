-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_finite_grid_girsanov_constant_shift
-- name    : AppliedSDE.SarkkaSolin.finite_grid_girsanov_constant_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:47:31.076453+00:00
-- url     : https://prove2.me/theorems/6925f1c0-a4dc-4eaf-bad2-0ca79a8f3ffd
-- title:
--   Finite-grid constant-drift Girsanov likelihood-ratio identity
-- statement:
--   Theorem 7.7, equations (7.43)–(7.46), printed p. 107. For an arbitrary finite list of real increments dx, positive step lengths dt and a single fixed real drift-shift parameter θ, the product of exponential Gaussian drift-shift factors collapses to the exponential of total shifted increment minus quadratic action. This is a finite-dimensional algebraic constant-shift specialisation. Independence and Brownian-motion assumptions are not present in the formal theorem. The full adapted stochastic-integrand Girsanov theorem and changed-measure Brownian property remain to be formalised.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \prod_k e^{\,\theta\Delta x_k-\theta^2\Delta t_k/2}=\exp\!\left(\theta\sum_k\Delta x_k-\frac{\theta^2}{2}\sum_k\Delta t_k\right)
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.7, equations (7.43)–(7.46), finite-grid exponential identity, printed p. 107. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.finite_grid_girsanov_constant_shift
    (n : ℕ) (θ : ℝ) (dx dt : Fin n → ℝ)
    (hdt : ∀ k : Fin n, 0 < dt k) :
    (∏ k : Fin n, Real.exp (θ * dx k - θ ^ 2 / 2 * dt k)) =
      Real.exp (θ * (∑ k : Fin n, dx k) -
        θ ^ 2 / 2 * (∑ k : Fin n, dt k)) := by
  sorry
