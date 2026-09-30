-- Prove2me | Theorems.Thm_AllocationIndices_search_index_optimal
-- name    : AllocationIndices.search_index_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:40:28.984384+00:00
-- url     : https://prove2.me/theorems/7debe2ac-9027-4823-bc83-da54a83e649d
-- title:
--   Theorem 3.6 (Blackwell): the optimal policies for the search problem are exactly those conforming to the index p_i q_i / c_i
-- statement:
--   **Theorem 3.6.** Optimal policies for Problem 3 are those conforming to the index $p_i q_i / c_i$.
--
--   Formally: $n$ boxes, prior probabilities $p_i \ge 0$ with $\sum_i p_i = 1$, detection probabilities $0 < q_i \le 1$ and search costs $c_i > 0$. With the convention that the $p_i$ change by Bayes' theorem, so that after $N_i$ unsuccessful searches of box $i$ the current probability is proportional to $p_i(1-q_i)^{N_i}$, a search policy $\sigma$ (a sequence of boxes) is optimal, in the sense that no policy has a smaller expected cost of finding the object, if and only if at every step it searches a box whose current index $p'_i q_i / c_i$ is maximal.
--
--   The expected cost is $\sum_k c_{\sigma_k} \Pr[\text{not found by the first } k \text{ searches}]$ in $[0, \infty]$. The "only if" direction is part of the printed statement ("optimal policies are those …"): a policy that ever searches a box of strictly smaller index can be strictly improved by an interchange, and a policy that neglects a box of positive probability has infinite cost. Checked numerically: on random instances every single-step deviation from the index rule increased the cost.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §3.5.4 pp. 71-73, Problem 3, Problem 3A, (3.10)-(3.11) and Theorem 3.6 (Blackwell, reported by Matula 1964; also Exercise 3.6)

import Definitions.Def_AllocationIndices_Jobs

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem search_index_optimal {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n) :
    IsOptimalSearch p q c σ ↔ ConformsToSearchIndex p q c σ := by sorry

end AllocationIndices
