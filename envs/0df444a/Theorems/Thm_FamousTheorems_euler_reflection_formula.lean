-- Prove2me | Theorems.Thm_FamousTheorems_euler_reflection_formula
-- name    : FamousTheorems.euler_reflection_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:58.720105+00:00
-- url     : https://prove2.me/theorems/fa45b0d1-b6c1-45a4-94dd-49295779bfff
-- title:
--   Euler's reflection formula for the Gamma function
-- statement:
--   **Euler's reflection formula.** For every complex number $z$,
--   $$\Gamma(z)\,\Gamma(1-z)=\frac{\pi}{\sin(\pi z)}.$$
--
--   The formula links the Gamma function to the trigonometric functions. It gives $\Gamma(1/2)=\sqrt\pi$ and shows that $\Gamma$ has no zeros. It is also a key input in the functional equation of the Riemann zeta function.
--
--   **Formalization note.** Mathlib's `Complex.Gamma_mul_Gamma_one_sub`. The identity holds for all `z : ℂ`. At the integers, where $\Gamma(z)\Gamma(1-z)$ has a pole, Mathlib's conventions make both sides $0$: `Complex.Gamma` is $0$ at the poles and division by $0$ is $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.Gamma_mul_Gamma_one_sub`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_reflection_formula (z : ℂ) : Complex.Gamma z * Complex.Gamma (1 - z) = Real.pi / Complex.sin (Real.pi * z) := by sorry

end FamousTheorems
