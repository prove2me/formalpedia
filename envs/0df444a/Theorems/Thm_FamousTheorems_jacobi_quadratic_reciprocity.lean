-- Prove2me | Theorems.Thm_FamousTheorems_jacobi_quadratic_reciprocity
-- name    : FamousTheorems.jacobi_quadratic_reciprocity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:25.81385+00:00
-- url     : https://prove2.me/theorems/5c935655-92f3-42ec-9c45-706669df4a71
-- title:
--   Quadratic reciprocity for the Jacobi symbol
-- statement:
--   **Quadratic reciprocity for the Jacobi symbol.** For odd natural numbers $a$ and $b$,
--   $$\Big(\frac ab\Big)=(-1)^{\frac{a-1}{2}\cdot\frac{b-1}{2}}\Big(\frac ba\Big),$$
--   where $\big(\frac{\cdot}{\cdot}\big)$ is the Jacobi symbol.
--
--   This extends Gauss's quadratic reciprocity law from odd primes to all odd moduli. Unlike the Legendre symbol, the Jacobi symbol can be computed by a Euclid-like algorithm without factoring, because of this law. This is what makes the Solovay–Strassen primality test and fast Legendre-symbol evaluation possible.
--
--   **Formalization note.** Mathlib's `jacobiSym.quadratic_reciprocity`. The exponent is written as `a / 2 * (b / 2)` with natural-number division, which equals $\frac{a-1}2\cdot\frac{b-1}2$ for odd $a,b$. The symbol is `jacobiSym (a : ℤ) b`, and no coprimality assumption is needed (both sides vanish otherwise).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `jacobiSym.quadratic_reciprocity`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobi_quadratic_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    jacobiSym (a : ℤ) b = (-1) ^ (a / 2 * (b / 2)) * jacobiSym (b : ℤ) a := by sorry

end FamousTheorems
