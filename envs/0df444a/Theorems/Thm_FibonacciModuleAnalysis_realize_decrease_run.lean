-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_realize_decrease_run
-- name    : FibonacciModuleAnalysis.realize_decrease_run
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:56:53.312381+00:00
-- url     : https://prove2.me/theorems/6b3552a3-834a-418d-a8c2-91eaa6a64116
-- title:
--   Fibonacci heap: realize a mathematical decrease as a Call contract
-- statement:
--   For a `DecreaseRun` with specified before/after snapshots and cut count, a valid concrete layout representing the initial snapshot and a present target handle admit a final heap satisfying `UpdateContract`. The final snapshot is precisely the mathematical result. The run premise supplies the decrease operation's structural conditions.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L4789-L4890

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_decrease_effect_summary
import Theorems.Thm_FibonacciModuleAnalysis_realize_cascade_run

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.realize_decrease_run :
    ∀ (before after : Algo2Lean.Fibonacci.Snapshot) (vertex key : Int) (cuts : Nat),
      Algo2Lean.Fibonacci.DecreaseRun before after vertex key cuts →
        ∀ (heap : Algo2LeanGenerated.Heap)
          (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
          (layout : FibonacciModuleAnalysis.Layout),
          layout.Valid heap queue →
            Eq.{1} (FibonacciModuleAnalysis.snapshot heap layout) before →
              Ne.{1} (heap.read layout.present vertex) (0 : Int) →
                Exists.{1} fun finalHeap =>
                  Exists.{1} fun finalLayout =>
                    FibonacciModuleAnalysis.UpdateContract heap finalHeap queue layout finalLayout
                        vertex key cuts ∧
                      Eq.{1} (FibonacciModuleAnalysis.snapshot finalHeap finalLayout) after := by
  sorry
