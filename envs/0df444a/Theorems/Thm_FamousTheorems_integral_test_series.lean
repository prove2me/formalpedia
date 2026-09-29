-- Prove2me | Theorems.Thm_FamousTheorems_integral_test_series
-- name    : FamousTheorems.integral_test_series
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:51.027803+00:00
-- url     : https://prove2.me/theorems/21adec7c-b539-4da5-ba08-2ad728450194
-- title:
--   The integral test for series (convergence direction)
-- statement:
--   **The integral test for series (convergence direction).** Let $f:\mathbb R\to\mathbb R$ be nonnegative and nonincreasing on $[N,\infty)$ for some natural number $N$. If $f$ is integrable on $(N,\infty)$, then the series $\sum_{n\ge0}f(n)$ converges.
--
--   The integral test compares a series with an integral. It gives the convergence of $\sum1/n^s$ for $s>1$ and the convergence and divergence of the Bertrand series $\sum1/(n\log^\alpha n)$. Its converse direction (divergence of the integral implies divergence of the series) is a separate Mathlib result and is not part of this statement.
--
--   **Formalization note.** Mathlib's `AntitoneOn.summable_of_integrableOn_Ioi`. Integrability is Lebesgue integrability on `Set.Ioi N` (`IntegrableOn`), and convergence is `Summable` of $n\mapsto f(n)$ for real-valued terms. Since the terms are nonnegative, this is the same as convergence of the partial sums.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AntitoneOn.summable_of_integrableOn_Ioi`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem integral_test_series {f : ℝ → ℝ} {N : ℕ} (hf : AntitoneOn f (Set.Ici (N : ℝ))) (hint : IntegrableOn f (Set.Ioi (N : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ f t) : Summable fun n : ℕ => f n := by sorry

end FamousTheorems
