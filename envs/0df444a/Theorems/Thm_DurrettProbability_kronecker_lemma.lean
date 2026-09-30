-- Prove2me | Theorems.Thm_DurrettProbability_kronecker_lemma
-- name    : DurrettProbability.kronecker_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T17:03:49.696185+00:00
-- url     : https://prove2.me/theorems/7bc7c34d-c44f-4161-9212-cf698f4b6016
-- title:
--   Theorem 2.5.9 — Kronecker's lemma
-- statement:
--   Let $(a_n)$ be a positive increasing sequence with $a_n\to\infty$, and let $(x_n)$ be real
--   numbers. If the series $\sum_n x_n/a_n$ converges, then
--   $$\frac{1}{a_n}\sum_{m\le n}x_m\longrightarrow0 .$$
--
--   There is no probability in this statement — it is a lemma about real sequences — but it is what
--   converts every theorem about convergence of random series into a theorem about averages, and
--   therefore the bridge from section 2.5 to the strong law of large numbers. Applying the three-series
--   theorem to $X_n/n$ and then Kronecker's lemma with $a_n=n$ turns "$\sum_n X_n/n$ converges" into
--   "$S_n/n\to0$", which is the law of large numbers.
--
--   The proof is summation by parts: writing $b_m=\sum_{k\le m}x_k/a_k$ and $x_m=a_m(b_m-b_{m-1})$,
--   the average $a_n^{-1}\sum_{m\le n}x_m$ becomes $b_n$ minus a weighted average of $b_0,\dots,b_{n-1}$
--   with weights summing to one, and both converge to the same limit.
--
--   **Formalization Note** "Increases to infinity" is split into positivity, monotonicity and
--   divergence, since positivity is what makes the divisions meaningful and is used separately from the
--   other two. Convergence of $\sum_n x_n/a_n$ is convergence of the partial sums to a real limit, as
--   in the rest of this mission, and not absolute convergence — the hypothesis would otherwise be much
--   stronger than the book's and the lemma correspondingly weaker.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 85 (PDF p. 93), Theorem 2.5.9: 'Kronecker's lemma. If a_n increases to infinity and sum_{n=1}^{infinity} x_n/a_n converges then a_n^{-1} sum_{m=1}^{n} x_m -> 0.' Durrett introduces it as 'The link between convergence of series and the strong law of large numbers is provided by'. sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

theorem kronecker_lemma (a x : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (hamono : Monotone a)
    (hatop : Tendsto a atTop atTop)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, x n / a n) atTop (nhds L)) :
    Tendsto (fun n => (∑ m ∈ Finset.range n, x m) / a n) atTop (nhds 0) := by sorry

end DurrettProbability
