-- Prove2me | Theorems.Thm_CLRS_HeapSortIndices_correctness_and_running_time
-- name    : CLRS.HeapSortIndices.correctness_and_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-14T19:10:14.588769+00:00
-- url     : https://prove2.me/theorems/6949947e-bf08-4493-aed5-1f66cf83371b
-- title:
--   Indexed-heap sorting: correctness and uniform running-time bound
-- statement:
--   There is one positive natural-number constant C, independent of all inputs and initial counters, such that for every initial heap, allocated key sequence, and natural length n, Lunjia Hu's indexed-heap sort terminates and returns a fresh allocated sequence. Its first n entries are a permutation of 0, ..., n−1 in nondecreasing order of their original keys. Previously allocated caller sequences and objects, and all collections, are preserved. The same completed call satisfies the original per-clock Budget n (2n), and the sum of its sort_steps, heap_comparisons, and heap_swaps increments is at most C·(1+n·(1+floor(log₂(n+1)))). Duplicate and negative keys and n=0 are allowed; no stability is asserted. The result describes sorted identifiers, not in-place sorting of input values. The counted work is the named source events, not every primitive operation, bit complexity, or wall-clock time. This theorem is derived from the existing published SortIndicesAnalysis.call contract; its proof is retained locally for review.
-- source:
--   Derived from https://prove2.me/theorems/67476c98-cb75-466b-bdf8-6eb449ba7184; CLRS fourth edition, Chapter 6, §§6.1–6.2 and §6.5.

import Theorems.Thm_SortIndicesAnalysis_call

set_option autoImplicit false

open Algo2LeanGenerated

theorem CLRS.HeapSortIndices.correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (keys : SeqRef) (n : Nat), keys < heap.nextRef →
        ∃ after result,
          Algo.sort_indices.sort_indices.Call heap (keys, (n : Int)) after result ∧
          SortIndicesAnalysis.SortedPermutation (heap.read keys) (n : Int) (after.read result) ∧
          SortIndicesAnalysis.Preserves heap after ∧
          heap.nextRef ≤ result ∧ result < after.nextRef ∧
          SortIndicesAnalysis.Budget (n : Int) (2 * n) heap after ∧
          SortIndicesAnalysis.runtime (Heap.cost heap after) ≤
            C * (1 + n * (1 + Nat.log2 (n + 1))) := by
  sorry
