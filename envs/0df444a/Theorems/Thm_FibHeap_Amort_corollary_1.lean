-- Prove2me | Theorems.Thm_FibHeap_Amort_corollary_1
-- name    : FibHeap.Amort.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:17:32.597868+00:00
-- url     : https://prove2.me/theorems/fee1a72f-2771-4666-83bb-baccb40c57be
-- title:
--   COROLLARY 1, p. 604 — a node of rank k has at least F_{k+2} ≥ φ^k descendants, including itself
-- statement:
--   Let $\mathcal S$ be a collection of F-heaps obtained from no heaps by an arbitrary sequence of F-heap operations, and let $x$ be a node of rank $k$ in a heap of $\mathcal S$. Write $\mathrm{size}(x)$ for the number of descendants of $x$, including $x$ itself, $F_k$ for the $k$th Fibonacci number ($F_0 = 0$, $F_1 = 1$, $F_k = F_{k-2} + F_{k-1}$ for $k \ge 2$) and $\varphi = (1+\sqrt5)/2$ for the golden ratio. Then
--
--   $$\mathrm{size}(x) \;\ge\; F_{k+2} \;\ge\; \varphi^{k} .$$
--
--   This is the source of the name "Fibonacci heap": it bounds the rank of every node by a logarithm of the heap's size.
--
--   **Formalization Note** The statement quantifies over reachable collections only.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 604, COROLLARY 1

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem corollary_1 (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees,
      Nat.fib (x.rank + 2) ≤ x.size ∧
        Real.goldenRatio ^ x.rank ≤ (Nat.fib (x.rank + 2) : ℝ) := by sorry
end FibHeap.Amort
