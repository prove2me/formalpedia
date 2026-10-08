-- Prove2me | Theorems.Thm_FibHeap_Amort_potential_decreaseKey_le
-- name    : FibHeap.Amort.potential_decreaseKey_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:18:15.893829+00:00
-- url     : https://prove2.me/theorems/7b201787-b713-4ca2-b691-a32da00f7b8a
-- title:
--   §2, p. 604 — decrease key increases the potential by at most three minus the number of cascading cuts
-- statement:
--   Let $\Phi$ be the potential of a collection of F-heaps (number of trees plus twice the number of marked nonroot nodes). If a decrease key operation turns the collection $\mathcal S$ into $\mathcal S'$ and makes $c$ cascading cuts, then
--
--   $$\Phi(\mathcal S') + c \;\le\; \Phi(\mathcal S) + 3 .$$
--
--   With one unit charged per cut, decrease key costs $2 + c$ when the item is not in a root, so its amortized time is at most $5$.
--
--   **Formalization Note** No reachability hypothesis is needed: the bound holds for every collection on which the operation can be performed. When the item is in a root, no cut is made and $c = 0$.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), p. 604, §2, potential analysis of decrease key

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem potential_decreaseKey_le (s s' : Coll) (Δ : ℝ) (i h : ℕ) (d : StepData)
    (hstep : Step s (.decreaseKey Δ i h) s' d) :
    potential s' + d.cascading ≤ potential s + 3 := by sorry
end FibHeap.Amort
