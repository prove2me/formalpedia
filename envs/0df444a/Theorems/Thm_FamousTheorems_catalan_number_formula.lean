-- Prove2me | Theorems.Thm_FamousTheorems_catalan_number_formula
-- name    : FamousTheorems.catalan_number_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:49.925733+00:00
-- url     : https://prove2.me/theorems/f215d03e-13e9-4fa2-bdfa-4c8f8eb3fdae
-- title:
--   The Catalan number formula
-- statement:
--   **The Catalan number formula.** The $n$-th Catalan number satisfies
--   $$(n+1)\,C_n=\binom{2n}{n},\qquad\text{so}\qquad C_n=\frac1{n+1}\binom{2n}{n}.$$
--
--   Catalan numbers count well-formed bracket sequences, binary trees, triangulations of a convex polygon and many other structures. The closed formula is usually proved by the reflection principle or by generating functions.
--
--   **Formalization note.** Mathlib's `succ_mul_catalan_eq_centralBinom` and `catalan_eq_centralBinom_div`. Mathlib defines `catalan` by the recursion $C_{n+1}=\sum_{i\le n}C_iC_{n-i}$ with $C_0=1$, and `n.centralBinom` is $\binom{2n}n$. The division in the second part is natural-number division, which is exact by the first part.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `catalan_eq_centralBinom_div`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem catalan_number_formula (n : ℕ) : (n + 1) * catalan n = n.centralBinom ∧ catalan n = n.centralBinom / (n + 1) := by sorry

end FamousTheorems
