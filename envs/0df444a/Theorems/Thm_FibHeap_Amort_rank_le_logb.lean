-- Prove2me | Theorems.Thm_FibHeap_Amort_rank_le_logb
-- name    : FibHeap.Amort.rank_le_logb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:17:43.376585+00:00
-- url     : https://prove2.me/theorems/e480ee80-0ff5-46a9-94cf-a4b8e54466a1
-- title:
--   §2, p. 604, potential analysis of delete min — a node of rank k in an n-item heap has φ^k ≤ n, so k ≤ log n / log φ
-- statement:
--   Let $\mathcal S$ be a collection of F-heaps obtained from no heaps by an arbitrary sequence of F-heap operations, let $h$ be a heap of $\mathcal S$ with $n$ items, and let $x$ be a node of $h$ of rank $k$. Then
--
--   $$\varphi^{k} \le n \qquad\text{and}\qquad k \le \frac{\log n}{\log \varphi},$$
--
--   where $\varphi = (1+\sqrt5)/2$.
--
--   This bounds the rank of every node, in particular of the minimum node removed by delete min, by $O(\log n)$.
--
--   **Formalization Note** The paper states this for the minimum node and continues "$\le 1.4404 \log n$". That last constant is a rounding slip: $1/\log_2\varphi = 1.44042\ldots > 1.4404$, and a node of rank $k$ can sit in a heap of $n = F_{k+2}$ items, for which $k > 1.4404 \log_2 n$ once $k$ is large. The statement therefore keeps the exact bound $\log_\varphi n$, and it is stated for every node, which is what the analysis of delete needs.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 604, §2, potential analysis of delete min

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem rank_le_logb (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Real.goldenRatio ^ x.rank ≤ (heapSize r : ℝ) ∧
        (x.rank : ℝ) ≤ Real.logb Real.goldenRatio (heapSize r) := by sorry
end FibHeap.Amort
