-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_decrease_effect_summary
-- name    : FibonacciModuleAnalysis.decrease_effect_summary
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:55:03.53+00:00
-- url     : https://prove2.me/theorems/560233e4-9f77-40ef-a9eb-7774e3dfc55c
-- title:
--   Fibonacci heap: a local decrease effect realizes a compiled call
-- statement:
--   Assume a valid layout, a present handle v, a strictly smaller new key k, and a `DecreaseEffect` from the heap with k installed to the specified final heap/layout with c cuts. Then the actual push_or_decrease method has a Call to that final heap. This realizes a supplied finite local effect; existence and bounds for the effect are proved separately.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L1877-L1977

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_cut_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.decrease_effect_summary :
    ∀ (heap after : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout finalLayout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (vertex key : Int),
          Ne.{1} (heap.read layout.present vertex) (0 : Int) →
            LT.lt.{0} key (heap.read layout.keys vertex) →
              ∀ (cuts : Nat),
                FibonacciModuleAnalysis.DecreaseEffect queue vertex key
                    (FibonacciModuleAnalysis.lowerKeyHeap heap layout vertex key) layout after
                    finalLayout cuts →
                  Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                    (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () := by
  sorry
