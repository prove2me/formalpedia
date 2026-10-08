-- Prove2me | Theorems.Thm_FibHeap_Amort_potential_makeHeap_findMin_insert_meld
-- name    : FibHeap.Amort.potential_makeHeap_findMin_insert_meld
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:17:52.912348+00:00
-- url     : https://prove2.me/theorems/80db3e09-eef3-4fac-9972-273b2b889ab0
-- title:
--   §2, pp. 600–601 and 604 — make heap, find min and meld leave the potential unchanged; insert raises it by one
-- statement:
--   Let $\Phi$ be the potential of a collection of F-heaps: the number of trees plus twice the number of marked nonroot nodes. If a collection $\mathcal S$ becomes $\mathcal S'$ by one operation, then
--
--   1. for a make heap, find min or meld operation, $\Phi(\mathcal S') = \Phi(\mathcal S)$;
--   2. for an insert operation, $\Phi(\mathcal S') = \Phi(\mathcal S) + 1$.
--
--   Since each of these operations costs one unit, their amortized time is $O(1)$.
--
--   **Formalization Note** No reachability hypothesis is needed: the identity holds for every collection on which the operation can be performed.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), pp. 600–601 and p. 604, §2

import Mathlib
import Definitions.Def_FibHeap_Amort_Model

namespace FibHeap.Amort
theorem potential_makeHeap_findMin_insert_meld (s s' : Coll) (op : Op) (d : StepData)
    (hstep : Step s op s' d) :
    ((op = .makeHeap ∨ (∃ h, op = .findMin h) ∨ (∃ h₁ h₂, op = .meld h₁ h₂)) →
        potential s' = potential s) ∧
      (∀ (i : ℕ) (k : ℝ) (h : ℕ), op = .insert i k h →
        potential s' = potential s + 1) := by sorry
end FibHeap.Amort
