-- Prove2me | Theorems.Thm_FibHeap_Amort_theorem_1
-- name    : FibHeap.Amort.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:17:32.737849+00:00
-- url     : https://prove2.me/theorems/e5df9ef8-cd05-4ed0-a99c-9597581130de
-- title:
--   THEOREM 1, p. 604 — from no F-heaps, total time ≤ Σ C(log n + 1) over delete min/delete + Σ C over other operations
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Begin with no F-heaps and perform an arbitrary sequence of $T$ F-heap operations $o_0, \ldots, o_{T-1}$ (make heap, find min, insert, meld, delete min, decrease key, delete), passing through collections $\mathcal S_0 = \emptyset, \mathcal S_1, \ldots, \mathcal S_T$. Let $\mathrm{cost}_t$ be the actual time of $o_t$: one unit, plus one per linking step, plus one per cut, plus the rank scan of a delete min. Then
--
--   $$\sum_{t=0}^{T-1} \mathrm{cost}_t \;\le\; \sum_{t=0}^{T-1} b_t, \qquad b_t = \begin{cases} C\,(\log_2 n_t + 1) & \text{if } o_t \text{ is a delete min or delete on heap } h_t,\\ C & \text{otherwise,}\end{cases}$$
--
--   where $n_t$ is the number of items in $h_t$ just before $o_t$.
--
--   This is the paper's statement that the total time is at most the total amortized time, where the amortized time is $O(\log n)$ for delete min and delete and $O(1)$ for every other operation. It is what yields the $O(n \log n + m)$ bound for Dijkstra's algorithm and the other network-optimization bounds of the paper.
--
--   **Formalization Note** The $O(\cdot)$ is pinned to one constant $C$ chosen before the sequence of operations. The cost counts every linking step and every cut, as fixed by the step relation; the potential does not appear in the statement. The linking order and the choice among minimum-key roots are arbitrary, and the bound must hold for every choice.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 604, THEOREM 1

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData),
      IsRun T s op d →
        (∑ t ∈ Finset.range T, (cost (d t) : ℝ)) ≤
          ∑ t ∈ Finset.range T, opBound C (s t) (op t) := by sorry
end FibHeap.Amort
