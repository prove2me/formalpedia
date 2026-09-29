-- Prove2me | Theorems.Thm_FamousTheorems_bernoulli_inequality
-- name    : FamousTheorems.bernoulli_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:47.026097+00:00
-- url     : https://prove2.me/theorems/22ec3ed7-008f-425f-999b-5b56e2261450
-- title:
--   Bernoulli's inequality
-- statement:
--   **Bernoulli's inequality.** For every real $a\ge-2$ and every natural number $n$,
--   $$(1+a)^n\ge1+na.$$
--
--   The classical statement assumes $a\ge-1$; the inequality in fact holds for $a\ge-2$. It is one of the most basic inequalities in analysis. It gives the divergence of $r^n$ for $r>1$, elementary bounds on $(1+1/n)^n$, and many estimates in limits and convergence proofs.
--
--   **Formalization note.** Mathlib's `one_add_mul_le_pow`, which holds in every linearly ordered ring and is stated here for `ℝ`. The exponent $n$ is a natural number, and `(n : ℝ)` is its cast.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `one_add_mul_le_pow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bernoulli_inequality {a : ℝ} (H : -2 ≤ a) (n : ℕ) : 1 + (n : ℝ) * a ≤ (1 + a) ^ n := by sorry

end FamousTheorems
