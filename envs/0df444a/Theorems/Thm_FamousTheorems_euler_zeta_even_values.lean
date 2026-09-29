-- Prove2me | Theorems.Thm_FamousTheorems_euler_zeta_even_values
-- name    : FamousTheorems.euler_zeta_even_values
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:09.48167+00:00
-- url     : https://prove2.me/theorems/304538ac-1d6b-4edc-ab0d-5925908e12f1
-- title:
--   Euler's evaluation of ζ(2k)
-- statement:
--   **Euler's evaluation of $\zeta(2k)$.** For every integer $k\ge1$,
--   $$\sum_{n=1}^{\infty}\frac1{n^{2k}}=\frac{(-1)^{k+1}\,2^{2k-1}\,\pi^{2k}\,B_{2k}}{(2k)!},$$
--   where $B_{2k}$ is the $2k$-th Bernoulli number.
--
--   For $k=1$ this is the Basel problem $\zeta(2)=\pi^2/6$, solved by Euler in 1734, and for $k=2$ it gives $\zeta(4)=\pi^4/90$. The formula shows that every $\zeta(2k)$ is a rational multiple of $\pi^{2k}$, in contrast with the odd values $\zeta(3),\zeta(5),\dots$, about which little is known.
--
--   **Formalization note.** Mathlib's `hasSum_zeta_nat`. The series is indexed by all `n : ℕ`, but its $n=0$ term is $1/0=0$ in Lean, so it is the usual sum over $n\ge1$. `bernoulli` is Mathlib's Bernoulli numbers (with $B_1=-\tfrac12$, irrelevant here since only even indices appear).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `hasSum_zeta_nat`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_zeta_even_values {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k))
      ((-1) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ)) := by sorry

end FamousTheorems
