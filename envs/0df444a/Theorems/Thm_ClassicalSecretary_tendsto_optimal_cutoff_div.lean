-- Prove2me | Theorems.Thm_ClassicalSecretary_tendsto_optimal_cutoff_div
-- name    : ClassicalSecretary.tendsto_optimal_cutoff_div
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:53:51.435308+00:00
-- url     : https://prove2.me/theorems/c5388fac-4cb8-430b-9906-d71ee29df721
-- title:
--   The optimal cutoff is asymptotically $n/e$
-- statement:
--   Let $(r_n)$ be a sequence such that, for every $n \ge 1$, $1 \le r_n \le n$ and the cutoff rule with cutoff $r_n$ is optimal, i.e. $P_n(\text{cutoff } r_n) = V_n$. Then
--   $$\lim_{n\to\infty}\frac{r_n}{n} = \frac1e .$$
--
--   The statement holds for every choice of optimal cutoffs (for small $n$ the optimal cutoff need not be unique).
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy": "Thus, the optimal cutoff tends to n/e as n increases".

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem tendsto_optimal_cutoff_div (r : ℕ → ℕ)
    (hr : ∀ n : ℕ, 1 ≤ n →
      1 ≤ r n ∧ r n ≤ n ∧ successProb n (cutoffRule (r n)) = optimalProb n) :
    Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ)) atTop (𝓝 (Real.exp (-1))) := by sorry

end ClassicalSecretary
