-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_bridge_doob_h_drift
-- name    : AppliedSDE.SarkkaSolin.brownian_bridge_doob_h_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:47:43.343504+00:00
-- url     : https://prove2.me/theorems/fc8498f5-72be-478c-88d8-85232cd6e998
-- title:
--   Doob h-transform drift of the scalar Brownian bridge
-- statement:
--   Theorem 7.11, equation (7.79), printed p. 115. In the constant-diffusion, zero-drift case, the terminal-state Gaussian transition density h(t,x)=p(z,T | x,t) has logarithmic spatial derivative (z-x)/(q(T-t)). Therefore the diffusion drift correction q∇log h is (z-x)/(T-t), the Brownian bridge drift. This is a nontrivial specialisation of the general endpoint-conditioned diffusion theorem.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   q\,\partial_x\log p(z,T\mid x,t)=\frac{z-x}{T-t}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.11, equation (7.79), Brownian-bridge specialisation, printed p. 115. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.brownian_bridge_doob_h_drift
    (q T t x z : ℝ) (hq : 0 < q) (ht : t < T) :
    let h : ℝ → ℝ := fun u =>
      Real.exp (-((z - u) ^ 2 / (2 * q * (T - t)))) /
        Real.sqrt (2 * Real.pi * q * (T - t))
    q * deriv (fun u => Real.log (h u)) x = (z - x) / (T - t) := by
  sorry
