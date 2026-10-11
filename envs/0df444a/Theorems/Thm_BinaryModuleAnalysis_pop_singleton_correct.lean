-- Prove2me | Theorems.Thm_BinaryModuleAnalysis_pop_singleton_correct
-- name    : BinaryModuleAnalysis.pop_singleton_correct
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:27.458897+00:00
-- url     : https://prove2.me/theorems/e01961c1-366e-4825-9dd7-760edc1287de
-- title:
--   Indexed binary heap: minimum extraction from a singleton
-- statement:
--   For `QueueRep heap queue layout` with size exactly one, `MinHeap.pop_min.Call` terminates and returns the vertex at position zero. Its `Extracted` postcondition establishes that this vertex was a minimum, removes exactly that vertex, leaves an empty represented queue, preserves all keys and unrelated storage, and bounds the two heap clocks. In this case no comparison is charged and at most one swap is charged.
--
--   This base case is used together with the non-singleton extraction theorem by clients such as index sorting.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/indexed_heap.lean#L2296-L2326

import Definitions.Def_Algo_indexed_heap_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem BinaryModuleAnalysis.pop_singleton_correct :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout),
      BinaryModuleAnalysis.QueueRep heap queue layout →
        Eq.{1} layout.size (1 : Int) →
          Exists.{1} fun after =>
            Algo.indexed_heap.MinHeap.pop_min.Call heap queue after
                (heap.read layout.vertices (0 : Int)) ∧
              BinaryModuleAnalysis.Extracted heap after queue layout
                (heap.read layout.vertices (0 : Int)) := by
  sorry
