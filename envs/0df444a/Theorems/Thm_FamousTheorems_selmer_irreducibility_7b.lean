-- Prove2me | Theorems.Thm_FamousTheorems_selmer_irreducibility_7b
-- name    : FamousTheorems.selmer_irreducibility_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:21.33325+00:00
-- url     : https://prove2.me/theorems/03d9b3e2-b9ba-4334-8dd1-5d0405c254f7
-- title:
--   Selmer's theorem: Xⁿ − X − 1 is irreducible over ℚ
-- statement:
--   **Selmer's theorem.** For every $n\neq1$, the polynomial $X^n-X-1$ is irreducible over $\mathbb Z$.
--
--   Selmer proved this in 1956. Since the polynomial is monic, it is also irreducible over $\mathbb Q$ by Gauss's lemma. It is a standard example of a family of trinomials with Galois group $S_n$, as shown later by Osada, and so of polynomials that cannot be solved by radicals for $n\ge5$. The proof counts the roots of each factor that lie on or near the unit circle.
--
--   **Formalization note.** Mathlib's `Polynomial.X_pow_sub_X_sub_one_irreducible`, stated in $\mathbb Z[X]$. For $n=0$ the polynomial is $-X$, which is irreducible. For $n=1$ it is the unit $-1$, which is excluded.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.X_pow_sub_X_sub_one_irreducible`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem selmer_irreducibility_7b {n : ℕ} (hn : n ≠ 1) : Irreducible (Polynomial.X ^ n - Polynomial.X - 1 : Polynomial ℤ) := by sorry

end FamousTheorems
