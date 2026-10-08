-- Prove2me | Theorems.Thm_FibHeap_Amort_sum_cost_le_sum_amortized
-- name    : FibHeap.Amort.sum_cost_le_sum_amortized
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:17:37.862292+00:00
-- url     : https://prove2.me/theorems/1dd8ba13-4f59-44f2-841c-00174250754a
-- title:
--   §2, p. 600 — from no heaps, the total amortized time bounds the total actual time
-- statement:
--   Consider a sequence of $T$ F-heap operations starting from no heaps, passing through collections $\mathcal S_0 = \emptyset, \mathcal S_1, \ldots, \mathcal S_T$. Let $\mathrm{cost}_t$ be the actual time of the $t$th operation and $a_t = \mathrm{cost}_t + \Phi(\mathcal S_{t+1}) - \Phi(\mathcal S_t)$ its amortized time, where $\Phi$ is the potential (number of trees plus twice the number of marked nonroot nodes). Then
--
--   $$\sum_{t=0}^{T-1} \mathrm{cost}_t \;\le\; \sum_{t=0}^{T-1} a_t .$$
--
--   The reason is that the initial potential is zero and the potential is always nonnegative.
--
--   **Formalization Note** The paper makes this remark on p. 600 for the potential "number of trees"; p. 604 extends the potential by twice the number of marked nonroot nodes, and the statement is about the extended potential.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 600, §2 (potential technique), with the potential of p. 604

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem sum_cost_le_sum_amortized (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData)
    (hrun : IsRun T s op d) :
    (∑ t ∈ Finset.range T, (cost (d t) : ℤ)) ≤
      ∑ t ∈ Finset.range T, amortized (d t) (s t) (s (t + 1)) := by sorry
end FibHeap.Amort
