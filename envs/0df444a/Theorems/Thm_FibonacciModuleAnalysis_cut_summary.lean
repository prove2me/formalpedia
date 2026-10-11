-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_cut_summary
-- name    : FibonacciModuleAnalysis.cut_summary
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:42.807669+00:00
-- url     : https://prove2.me/theorems/47ea2949-6ba2-4e4c-8b4b-88ea640d2b73
-- title:
--   Fibonacci heap: exact compiled cut operation
-- statement:
--   For a valid layout, the compiled `FibonacciHeap.cut` call on a child and parent reaches `cutHeap`. This theorem describes the local heap effect. Its premise does not assert a well-formed child/parent relationship; the forest-level cut theorem supplies those structural conditions when it is used.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L687-L749

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.cut_summary :
    ∀ (heap : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (vertex parent : Int),
          Algo.fibonacci_heap.FibonacciHeap.cut.Call heap
            (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex parent))
            (FibonacciModuleAnalysis.cutHeap heap queue layout vertex parent) () := by
  sorry
