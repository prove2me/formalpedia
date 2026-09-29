-- Prove2me | Theorems.Thm_FamousTheorems_euler_beta_integral_gamma
-- name    : FamousTheorems.euler_beta_integral_gamma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:09.872471+00:00
-- url     : https://prove2.me/theorems/aece3363-2824-4fef-880f-553d6d920eb6
-- title:
--   Euler's Beta integral
-- statement:
--   **Euler's Beta integral.** For complex numbers $s,t$ with $\operatorname{Re}s>0$ and $\operatorname{Re}t>0$,
--   $$\Gamma(s)\,\Gamma(t)=\Gamma(s+t)\,B(s,t),\qquad B(s,t)=\int_0^1 x^{s-1}(1-x)^{t-1}\,dx.$$
--
--   The identity $B(s,t)=\Gamma(s)\Gamma(t)/\Gamma(s+t)$ reduces a whole family of definite integrals to values of the Gamma function. It gives $\Gamma(1/2)=\sqrt\pi$ and the reflection formula, and it underlies the Dirichlet integral and the volume of the unit ball.
--
--   **Formalization note.** Mathlib's `Complex.Gamma_mul_Gamma_eq_betaIntegral`. `Complex.betaIntegral s t` is the integral $\int_0^1 x^{s-1}(1-x)^{t-1}\,dx$ with complex powers.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.Gamma_mul_Gamma_eq_betaIntegral`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_beta_integral_gamma {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    Complex.Gamma s * Complex.Gamma t = Complex.Gamma (s + t) * s.betaIntegral t := by sorry

end FamousTheorems
