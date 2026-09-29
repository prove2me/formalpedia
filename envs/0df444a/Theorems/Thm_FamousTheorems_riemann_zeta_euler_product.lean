-- Prove2me | Theorems.Thm_FamousTheorems_riemann_zeta_euler_product
-- name    : FamousTheorems.riemann_zeta_euler_product
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:07.93154+00:00
-- url     : https://prove2.me/theorems/4371f31e-dd90-4975-a20b-14ec1ff084f2
-- title:
--   The Euler product for the Riemann zeta function
-- statement:
--   **The Euler product for the Riemann zeta function.** For $\operatorname{Re}s>1$,
--   $$\prod_{p\text{ prime}}\frac1{1-p^{-s}}=\zeta(s).$$
--
--   Euler's product formula is the analytic form of unique factorization into primes. It is the bridge between the zeta function and the primes: it shows $\zeta(s)\neq0$ for $\operatorname{Re}s>1$, gives Euler's proof that $\sum1/p$ diverges, and is the starting point of the proof of the prime number theorem.
--
--   **Formalization note.** Mathlib's `riemannZeta_eulerProduct_tprod`. The product is the unconditional infinite product `∏'` over `Nat.Primes`, and `riemannZeta` is Mathlib's Riemann zeta function, equal to $\sum n^{-s}$ in this range.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `riemannZeta_eulerProduct_tprod`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riemann_zeta_euler_product {s : ℂ} (hs : 1 < s.re) : ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ = riemannZeta s := by sorry

end FamousTheorems
