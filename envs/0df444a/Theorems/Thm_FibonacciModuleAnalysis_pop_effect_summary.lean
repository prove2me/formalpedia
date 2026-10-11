-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_pop_effect_summary
-- name    : FibonacciModuleAnalysis.pop_effect_summary
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:54:00.347917+00:00
-- url     : https://prove2.me/theorems/4fb97640-a0e7-434e-89a4-5df9be865cae
-- title:
--   Fibonacci heap: a finite extraction effect realizes a compiled call
-- statement:
--   For a valid heap layout, any `PopEffect` describing a finite promotion/extraction sequence to a final heap yields `FibonacciHeap.pop_min.Call` with the stated output. The effect carries the necessary consolidation call. This is a local realization theorem; representation and amortized bounds are provided by the higher-level extraction contract.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L1629-L1765

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.pop_effect_summary :
    ∀ (heap after : Algo2LeanGenerated.Heap)
      (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
      (layout finalLayout : FibonacciModuleAnalysis.Layout),
      layout.Valid heap queue →
        ∀ (output : Int) (count : Nat),
          FibonacciModuleAnalysis.PopEffect queue heap layout after finalLayout output count →
            Algo.fibonacci_heap.FibonacciHeap.pop_min.Call heap queue after output := by
  sorry
