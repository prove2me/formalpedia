-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_new_heap_representation
-- name    : FibonacciModuleAnalysis.new_heap_representation
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:51:21.954874+00:00
-- url     : https://prove2.me/theorems/4af82abd-112b-4f78-af23-2e71d60446c4
-- title:
--   Fibonacci heap: a fresh empty queue satisfies its representation
-- statement:
--   For every initial heap h, `newHeap h` contains a valid empty Fibonacci queue at h.nextObject with `emptyLayout h`. The finite forest is empty. This representation lemma supplies the starting invariant for compiled queue calls; it does not by itself assert a constructor execution.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L1089-L1092

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.new_heap_representation :
    ∀ (heap : Algo2LeanGenerated.Heap),
      FibonacciModuleAnalysis.QueueRep (FibonacciModuleAnalysis.newHeap heap) heap.nextObject
        (FibonacciModuleAnalysis.emptyLayout heap) List.nil.{0} := by
  sorry
