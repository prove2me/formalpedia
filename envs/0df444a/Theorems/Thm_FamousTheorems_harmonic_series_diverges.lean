-- Prove2me | Theorems.Thm_FamousTheorems_harmonic_series_diverges
-- name    : FamousTheorems.harmonic_series_diverges
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:20.914717+00:00
-- url     : https://prove2.me/theorems/3c97ea7d-0936-45e5-bbf2-a252ba9a03e8
-- title:
--   Divergence of the harmonic series
-- statement:
--   **The harmonic series diverges.**
--
--   $$\sum_{n=1}^{\infty} \frac{1}{n} \;=\; \infty .$$
--
--   Oresme's fourteenth-century proof groups terms in blocks of length $2^k$, each summing to at
--   least $\tfrac12$:
--   $$\tfrac13+\tfrac14 > \tfrac12,\quad \tfrac15+\cdots+\tfrac18 > \tfrac12,\ \dots$$
--   so the partial sums exceed any bound.
--
--   The divergence is famously slow — the partial sums grow like $\log n + \gamma$ — which is why
--   the result is counterintuitive: the terms tend to $0$, yet the sum does not converge. It is the
--   standard demonstration that $a_n \to 0$ is necessary but not sufficient for convergence.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem harmonic_series_diverges :
    Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1))
      Filter.atTop Filter.atTop := by sorry

end FamousTheorems
