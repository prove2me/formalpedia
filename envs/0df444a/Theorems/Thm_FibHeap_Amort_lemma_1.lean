-- Prove2me | Theorems.Thm_FibHeap_Amort_lemma_1
-- name    : FibHeap.Amort.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:17:11.064983+00:00
-- url     : https://prove2.me/theorems/8e8bbb35-7bff-45bc-8e02-5689eedf40f5
-- title:
--   LEMMA 1, p. 604 — the ith child of a node, in linking order, has rank at least i − 2
-- statement:
--   Let $\mathcal S$ be a collection of F-heaps obtained from no heaps by an arbitrary sequence of F-heap operations. Let $x$ be any node in a heap of $\mathcal S$, and arrange the children of $x$ in the order in which they were linked to $x$, from earliest to latest. Then for every $i \ge 1$ up to the rank of $x$, the $i$th child $y_i$ of $x$ satisfies
--
--   $$r(y_i) \;\ge\; i - 2 .$$
--
--   This lemma is what forces every tree of an F-heap, although not necessarily a binomial tree, to have size exponential in the rank of its root (Corollary 1).
--
--   **Formalization Note** Children are stored in linking order, so the $i$th child is the list entry at index $j = i - 1$. The inequality is written $j + 1 \le r(y) + 2$ to avoid truncated natural-number subtraction. The statement quantifies over reachable collections only; for arbitrary forests it is false.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 604, LEMMA 1

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem lemma_1 (s : Coll) (hs : Reachable s) :
    ∀ r ∈ s, ∀ τ ∈ r, ∀ x ∈ τ.subtrees, ∀ (j : ℕ) (hj : j < x.children.length),
      j + 1 ≤ (x.children[j]'hj).rank + 2 := by sorry
end FibHeap.Amort
