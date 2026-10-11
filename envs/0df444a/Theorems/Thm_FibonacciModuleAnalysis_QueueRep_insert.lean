-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_QueueRep_insert
-- name    : FibonacciModuleAnalysis.QueueRep.insert
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:54:02.161204+00:00
-- url     : https://prove2.me/theorems/ef3d7101-fbde-4f38-87dc-25d7fe963dac
-- title:
--   Fibonacci heap: fresh insertion preserves the represented forest
-- statement:
--   Given `QueueRep`, a nonnegative handle v absent from the presence array, and an integer key k, push_or_decrease has a terminating Call whose entries are a permutation of (v,k) followed by the previous entries. The final queue is represented, its root count increases by one, and its marked-node count is unchanged. The theorem concerns fresh insertion; existing handles use the decrease result.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L3611-L3637

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_add_root_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.QueueRep.insert :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        ∀ (vertex key : Int),
          LE.le.{0} (0 : Int) vertex →
            Eq.{1} (heap.read layout.present vertex) (0 : Int) →
              Exists.{1} fun afterForest =>
                Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                    (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key))
                    (FibonacciModuleAnalysis.insertionHeap heap queue layout vertex key) () ∧
                  FibonacciModuleAnalysis.QueueRep
                      (FibonacciModuleAnalysis.insertionHeap heap queue layout vertex key) queue
                      (FibonacciModuleAnalysis.insertionLayout heap queue layout vertex key)
                      afterForest ∧
                    List.Perm.{0} afterForest.entries
                        (List.cons.{0} (Prod.mk.{0, 0} vertex key) forest.entries) ∧
                      Eq.{1} (List.length.{0} afterForest)
                          (HAdd.hAdd.{0, 0, 0} (List.length.{0} forest) (1 : Nat)) ∧
                        Eq.{1} afterForest.marks forest.marks := by
  sorry
