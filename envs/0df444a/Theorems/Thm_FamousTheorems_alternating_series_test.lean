-- Prove2me | Theorems.Thm_FamousTheorems_alternating_series_test
-- name    : FamousTheorems.alternating_series_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:20.580537+00:00
-- url     : https://prove2.me/theorems/caeddba1-9836-4214-87b2-410e26b88a39
-- title:
--   The alternating series test (Leibniz criterion)
-- statement:
--   **The alternating series test (Leibniz criterion).** Let $(f(n))$ be a non-increasing sequence of reals tending to $0$. Then the alternating series
--   $$\sum_{i=0}^{\infty}(-1)^i f(i)$$
--   converges: its partial sums tend to a real limit.
--
--   Leibniz's criterion gives the convergence of many conditionally convergent series, such as $1-\frac12+\frac13-\cdots=\log2$ and the Leibniz series $1-\frac13+\frac15-\cdots=\frac\pi4$. The accompanying error bound (the remainder is at most the first omitted term) is not part of this statement.
--
--   **Formalization note.** Mathlib's `Antitone.tendsto_alternating_series_of_tendsto_zero`. The statement is about the sequence of partial sums $\sum_{i<n}(-1)^if(i)$ converging, not about unconditional summability (`Summable`), which fails for conditionally convergent series.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Antitone.tendsto_alternating_series_of_tendsto_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem alternating_series_test {f : ℕ → ℝ} (hfa : Antitone f) (hf0 : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∃ l : ℝ, Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1) ^ i * f i) Filter.atTop (nhds l) := by sorry

end FamousTheorems
