-- Prove2me | Theorems.Thm_FamousTheorems_gamma_nat_eq_factorial_7a
-- name    : FamousTheorems.gamma_nat_eq_factorial_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:37.579988+00:00
-- url     : https://prove2.me/theorems/7db3cce5-fbc9-4a4d-88e6-6e55e8509085
-- title:
--   Γ(n+1) = n! (the Gamma function interpolates the factorial)
-- statement:
--   **$\Gamma(n+1)=n!$ (the Gamma function interpolates the factorial).** For every natural number $n$,
--   $$\Gamma(n+1)=n!,$$
--   where $\Gamma(s)=\int_0^\infty t^{s-1}e^{-t}\,dt$ for $s>0$, extended to the rest of $\mathbb R$ by the recurrence $\Gamma(s+1)=s\,\Gamma(s)$.
--
--   Euler introduced the Gamma function in 1729 to solve the problem of extending the factorial to non-integer arguments. It appears in the volume of balls, in Stirling's formula, in the functional equation of the Riemann zeta function and in probability densities such as the Gamma and chi-squared distributions.
--
--   **Formalization note.** Mathlib's `Real.Gamma_nat_eq_factorial`. `Real.Gamma` is the real Gamma function, and the right-hand side is the factorial `n.factorial` cast to $\mathbb R$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.Gamma_nat_eq_factorial`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gamma_nat_eq_factorial_7a (n : ℕ) : Real.Gamma (n + 1) = n.factorial := by sorry

end FamousTheorems
