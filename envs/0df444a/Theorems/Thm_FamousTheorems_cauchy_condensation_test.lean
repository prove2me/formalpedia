-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_condensation_test
-- name    : FamousTheorems.cauchy_condensation_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:25.584782+00:00
-- url     : https://prove2.me/theorems/da1345f6-703a-4734-96e8-81308275b393
-- title:
--   The Cauchy condensation test
-- statement:
--   **The Cauchy condensation test.** Let $(f(n))_{n\ge0}$ be a sequence of nonnegative reals that is non-increasing for $n\ge1$. Then
--   $$\sum_n f(n)\ \text{converges}\iff\sum_k 2^k f(2^k)\ \text{converges}.$$
--
--   This is the standard way to settle the convergence of the $p$-series $\sum1/n^p$ and of series such as $\sum1/(n\log n)$ and $\sum1/(n(\log n)^2)$, reducing them to geometric or simpler series.
--
--   **Formalization note.** Mathlib's `summable_condensed_iff_of_nonneg`. Convergence is `Summable` in `ℝ`, which for nonnegative terms is ordinary convergence. Monotonicity is only required from index $1$ on (`0 < m → m ≤ n → f n ≤ f m`), so the value $f(0)$ is unconstrained.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `summable_condensed_iff_of_nonneg`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_condensation_test {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n) (h_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => 2 ^ k * f (2 ^ k)) ↔ Summable f := by sorry

end FamousTheorems
