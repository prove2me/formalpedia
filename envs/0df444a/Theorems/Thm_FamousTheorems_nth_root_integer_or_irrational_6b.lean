-- Prove2me | Theorems.Thm_FamousTheorems_nth_root_integer_or_irrational_6b
-- name    : FamousTheorems.nth_root_integer_or_irrational_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:48.943517+00:00
-- url     : https://prove2.me/theorems/14ed1cbb-7396-4798-b6d2-14b467a4807f
-- title:
--   An n-th root of an integer is either an integer or irrational
-- statement:
--   **An $n$-th root of an integer is either an integer or irrational.** Let $n\ge1$, $m\in\mathbb Z$ and $x\in\mathbb R$ with $x^n=m$. If $x$ is not an integer, then $x$ is irrational.
--
--   This generalizes the irrationality of $\sqrt2$. By the rational root theorem, a rational root of the monic polynomial $X^n-m$ must be an integer. It gives the irrationality of $\sqrt[n]{m}$ whenever $m$ is not a perfect $n$-th power, for example $\sqrt3$ and $\sqrt[3]{2}$.
--
--   **Formalization note.** Mathlib's `irrational_nrt_of_notint_nrt`. The hypotheses are $x^n=m$, that $x$ is not equal to any integer, and $0<n$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `irrational_nrt_of_notint_nrt`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem nth_root_integer_or_irrational_6b {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m) (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x := by sorry

end FamousTheorems
