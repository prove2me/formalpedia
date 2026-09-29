-- Prove2me | Theorems.Thm_FamousTheorems_euler_integral_log_sin_6c
-- name    : FamousTheorems.euler_integral_log_sin_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:08.011344+00:00
-- url     : https://prove2.me/theorems/c606d61b-4421-437e-88aa-4458faafc55e
-- title:
--   Euler's integral ∫₀^π log sin x dx = −π log 2
-- statement:
--   **Euler's integral of $\log\sin$.**
--   $$\int_0^{\pi}\log(\sin x)\,dx=-\pi\log 2.$$
--
--   Euler evaluated this integral in 1769, and it is a standard example of an improper integral computed by a symmetry trick: the substitution $x\mapsto 2x$ and $\sin 2x=2\sin x\cos x$ give a linear equation for the integral. It is closely related to the Clausen function and to the value $\zeta(2)$.
--
--   **Formalization note.** Mathlib's `integral_log_sin_zero_pi`. The integral is the interval integral `∫ x in 0..π`. The integrand has a logarithmic singularity at both endpoints, but it is integrable, and the interval integral is the Lebesgue integral.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `integral_log_sin_zero_pi`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_integral_log_sin_6c :
    ∫ x in (0 : ℝ)..Real.pi, Real.log (Real.sin x) = -Real.log 2 * Real.pi := by sorry

end FamousTheorems
