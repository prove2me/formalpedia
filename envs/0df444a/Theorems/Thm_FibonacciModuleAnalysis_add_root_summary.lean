-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_add_root_summary
-- name    : FibonacciModuleAnalysis.add_root_summary
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:51:46.46979+00:00
-- url     : https://prove2.me/theorems/28ebd5ba-43b3-4877-94ff-1b16c26d38dc
-- title:
--   Fibonacci heap: exact compiled root insertion
-- statement:
--   For any valid heap layout, queue reference and vertex, `FibonacciHeap.add_root.Call` reaches exactly `addRootHeap`. This local operational lemma describes the pointer updates. It requires layout validity; higher-level forest preservation is established by the queue representation theorems.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L438-L519

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.add_root_summary :
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (vertex : Int),
          Algo.fibonacci_heap.FibonacciHeap.add_root.Call heap (Prod.mk.{0, 0} queue vertex)
            (FibonacciModuleAnalysis.addRootHeap heap queue layout vertex) () := by
  sorry
