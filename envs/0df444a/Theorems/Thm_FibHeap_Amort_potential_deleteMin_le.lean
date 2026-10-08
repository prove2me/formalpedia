-- Prove2me | Theorems.Thm_FibHeap_Amort_potential_deleteMin_le
-- name    : FibHeap.Amort.potential_deleteMin_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:18:03.448023+00:00
-- url     : https://prove2.me/theorems/5092b826-6fe7-450b-abdb-9df7761593d8
-- title:
--   §2, p. 604 — delete min increases the potential by at most log n / log φ minus the number of linking steps
-- statement:
--   Let $\mathcal S$ be a collection of F-heaps obtained from no heaps by an arbitrary sequence of F-heap operations, and let $\Phi$ be the potential (number of trees plus twice the number of marked nonroot nodes). Suppose a delete min on the heap $h$, which holds $n$ items, turns $\mathcal S$ into $\mathcal S'$ using $L$ linking steps. Then
--
--   $$\Phi(\mathcal S') \;\le\; \Phi(\mathcal S) + \frac{\log n}{\log\varphi} - L ,$$
--
--   where $\varphi = (1+\sqrt5)/2$.
--
--   Together with the cost $1 + L + \mathrm{scan}$, this gives delete min an $O(\log n)$ amortized time.
--
--   **Formalization Note** The paper writes "at most $1.4404 \log n$ minus the number of linking steps". The constant $1.4404$ is a rounding slip ($1/\log_2\varphi = 1.44042\ldots$), with which the bound would be false for large heaps; the statement uses $\log_\varphi n = \log n / \log\varphi$, the quantity the paper's own argument produces.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 604, §2, potential analysis of delete min

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem potential_deleteMin_le (s s' : Coll) (hs : Reachable s) (h : ℕ) (d : StepData)
    (hstep : Step s (.deleteMin h) s' d) :
    (potential s' : ℝ) ≤
      potential s + Real.logb Real.goldenRatio (heapSize (s.getD h [])) - d.links := by sorry
end FibHeap.Amort
