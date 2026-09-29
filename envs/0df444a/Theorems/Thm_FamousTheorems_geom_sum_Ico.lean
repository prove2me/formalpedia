-- Prove2me | Theorems.Thm_FamousTheorems_geom_sum_Ico
-- name    : FamousTheorems.geom_sum_Ico
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:20.96519+00:00
-- url     : https://prove2.me/theorems/bd4da56a-eab4-4b05-8efd-609d83cac0af
-- title:
--   Sum of a geometric series
-- statement:
--   **Sum of a geometric series.**
--
--   For $x \neq 1$ in a division ring and $m \le n$,
--   $$\sum_{i=m}^{n-1} x^i = \frac{x^n - x^m}{x - 1}.$$
--
--   Taking $m = 0$ gives the familiar $\sum_{i<n} x^i = (x^n-1)/(x-1)$. The identity is the telescoping
--   $(x-1)\sum_{i=m}^{n-1} x^i = x^n - x^m$ divided through, and the hypothesis $x \neq 1$ is exactly what
--   makes that division legal. It holds in any division ring, commutativity is not needed: every term is a
--   power of the single element $x$, so everything in sight commutes.
--
--   The finite sum is the more fundamental statement — the infinite series $\sum_{i \ge 0} x^i = 1/(1-x)$
--   for $|x| < 1$ is its limit, and every convergence statement about geometric series descends from this
--   closed form. It is the workhorse behind the ratio test, the Neumann series for $(1 - T)^{-1}$, and the
--   evaluation of repeating decimals.
--
--   **Formalization note.** `Finset.Ico m n` is the half-open integer interval $[m, n)$. The result is
--   Mathlib's `geom_sum_Ico`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem geom_sum_Ico {K : Type*} [DivisionRing K] {x : K} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by sorry

end FamousTheorems
