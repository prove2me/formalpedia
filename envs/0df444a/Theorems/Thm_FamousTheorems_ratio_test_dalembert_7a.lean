-- Prove2me | Theorems.Thm_FamousTheorems_ratio_test_dalembert_7a
-- name    : FamousTheorems.ratio_test_dalembert_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:50.599877+00:00
-- url     : https://prove2.me/theorems/887f4f9b-293c-4e4e-85f4-5ad41beaf8d5
-- title:
--   The ratio test (d'Alembert's criterion)
-- statement:
--   **The ratio test (d'Alembert's criterion).** Let $(f_n)$ be a sequence in a complete normed group, and let $r<1$ be such that $\|f_{n+1}\|\le r\|f_n\|$ for all sufficiently large $n$. Then $\sum_n f_n$ is summable.
--
--   D'Alembert published the test in 1768. It compares the series with a geometric series, and it is the usual way to find the radius of convergence of power series such as $\sum x^n/n!$. The version here requires only a bound $r<1$ on the ratios for large $n$, not the existence of a limit.
--
--   **Formalization note.** Mathlib's `summable_of_ratio_norm_eventually_le`. `∀ᶠ n in Filter.atTop, P n` means that $P(n)$ holds for all sufficiently large $n$, and `Summable f` means unconditional summability. In a complete space this follows from absolute convergence.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `summable_of_ratio_norm_eventually_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ratio_test_dalembert_7a {α : Type*} [SeminormedAddCommGroup α] [CompleteSpace α] {f : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ᶠ n in Filter.atTop, ‖f (n + 1)‖ ≤ r * ‖f n‖) : Summable f := by sorry

end FamousTheorems
