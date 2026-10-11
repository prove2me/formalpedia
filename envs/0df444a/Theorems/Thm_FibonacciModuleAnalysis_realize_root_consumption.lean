-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_realize_root_consumption
-- name    : FibonacciModuleAnalysis.realize_root_consumption
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:54:12.29184+00:00
-- url     : https://prove2.me/theorems/78e42836-32a5-44b2-994f-4b0bd79a80de
-- title:
--   Fibonacci heap: realize root consumption and compose its reconstruction
-- statement:
--   Given a finite `RootConsumption` model run and a valid concrete layout whose snapshot equals the run's initial snapshot, there is an intermediate heap/layout with exactly the run's final snapshot. Any `RebuildEffect` from that intermediate state, using the run's final maximum and starting at degree zero, extends the result to `ConsumeEffect`. At the intermediate heap before rebuilding, r consumed roots and l links add exactly r root scans, l comparisons and l links to the existing counters, leaving other counters unchanged. The subsequent rebuild can add its own scans and comparisons.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L4150-L4205

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_realize_bucket_collisions

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.realize_root_consumption :
    ∀ (before after : Algo2Lean.Fibonacci.Snapshot) (maximum finalMaximum : Int) (roots links : Nat),
      Algo2Lean.Fibonacci.RootConsumption before maximum after finalMaximum roots links →
        ∀ (heap : Algo2LeanGenerated.Heap)
          (queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap)
          (layout : FibonacciModuleAnalysis.Layout),
          layout.Valid heap queue →
            Eq.{1} (FibonacciModuleAnalysis.snapshot heap layout) before →
              Exists.{1} fun tailHeap =>
                Exists.{1} fun tailLayout =>
                  tailLayout.Valid tailHeap queue ∧
                    Eq.{1} (FibonacciModuleAnalysis.snapshot tailHeap tailLayout) after ∧
                      (∀ (finalHeap : Algo2LeanGenerated.Heap)
                          (finalLayout : FibonacciModuleAnalysis.Layout),
                          FibonacciModuleAnalysis.RebuildEffect queue finalMaximum tailHeap tailLayout
                              (0 : Int) finalHeap finalLayout →
                            FibonacciModuleAnalysis.ConsumeEffect queue heap layout maximum finalHeap
                              finalLayout roots links) ∧
                        ∀ (clock : String),
                          Eq.{1} (tailHeap.clocks clock)
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (heap.clocks clock)
                                  (Algo2LeanGenerated.Clocks.single "heap_root_scans" roots clock))
                                (Algo2LeanGenerated.Clocks.single "heap_comparisons" links clock))
                              (Algo2LeanGenerated.Clocks.single "heap_links" links clock)) := by
  sorry
