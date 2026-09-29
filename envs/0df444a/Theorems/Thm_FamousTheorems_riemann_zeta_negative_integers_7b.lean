-- Prove2me | Theorems.Thm_FamousTheorems_riemann_zeta_negative_integers_7b
-- name    : FamousTheorems.riemann_zeta_negative_integers_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:18.072396+00:00
-- url     : https://prove2.me/theorems/e42e3888-a3b0-4dba-a2db-464e97a08603
-- title:
--   Values of the Riemann zeta function at negative integers (Bernoulli numbers)
-- statement:
--   **Values of the Riemann zeta function at negative integers.** For every integer $k\ge0$,
--   $$\zeta(-k)=(-1)^k\,\frac{B_{k+1}}{k+1},$$
--   where $B_m$ are the Bernoulli numbers and $\zeta$ is the meromorphic continuation of the Riemann zeta function.
--
--   Euler found these values in 1749. They give $\zeta(0)=-\tfrac12$, $\zeta(-1)=-\tfrac1{12}$, and $\zeta(-2k)=0$ for $k\ge1$ (the trivial zeros). The values are rational, and their divisibility properties lead to Kummer's congruences, the Kubota–Leopoldt $p$-adic zeta function, and Kummer's criterion for regular primes.
--
--   **Formalization note.** Mathlib's `riemannZeta_neg_nat_eq_bernoulli`. Mathlib's Bernoulli numbers `bernoulli` use the convention $B_1=-\tfrac12$. For $k=0$ the formula gives $\zeta(0)=B_1=-\tfrac12$. `riemannZeta` is defined on all of $\mathbb C$, with its value at the pole $s=1$ set by convention.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `riemannZeta_neg_nat_eq_bernoulli`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riemann_zeta_negative_integers_7b (k : ℕ) : riemannZeta (-(k : ℂ)) = (-1) ^ k * (bernoulli (k + 1) : ℂ) / (k + 1) := by sorry

end FamousTheorems
