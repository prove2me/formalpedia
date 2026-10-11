-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_QueueRep_decrease
-- name    : FibonacciModuleAnalysis.QueueRep.decrease
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:00:34.146798+00:00
-- url     : https://prove2.me/theorems/ef5d9e5d-6b39-4d76-9481-4fd9e34172cd
-- title:
--   Fibonacci heap: correctness and constant amortized running time for decrease-key
-- statement:
--   For a represented queue and a present handle with a strictly smaller new key, there is one compiled push_or_decrease Call that changes exactly that binding and preserves the queue representation. It preserves storage outside the queue's footprint, its allocation footprint, and all other clocks.
--
--   For measured heap-event work T and scaled potential Ψ,
--
--   $$T+\Psi(\mathrm{after})\leq\Psi(\mathrm{before})+20.$$
--
--   The potential belongs to the same before/after forests as the Call, allowing a client to telescope successive operations.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L4967-L4992

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_realize_decrease_run
import Theorems.Thm_Algo2Lean_Fibonacci_Decrease_amortized
import Theorems.Thm_Algo2Lean_Fibonacci_Represented_decrease

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.QueueRep.decrease :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        ∀ (vertex key : Int),
          Ne.{1} (heap.read layout.present vertex) (0 : Int) →
            LT.lt.{0} key (heap.read layout.keys vertex) →
              Exists.{1} fun after =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun afterForest =>
                    Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                        (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () ∧
                      FibonacciModuleAnalysis.QueueRep after queue finalLayout afterForest ∧
                        (∀ (v k : Int),
                            Membership.mem.{0, 0} afterForest.entries (Prod.mk.{0, 0} v k) ↔
                              Eq.{1} v vertex ∧ Eq.{1} k key ∨
                                Ne.{1} v vertex ∧
                                  Membership.mem.{0, 0} forest.entries (Prod.mk.{0, 0} v k)) ∧
                          heap.Modifies after layout.refs (List.cons.{0} queue List.nil.{0}) ∧
                            Eq.{1} finalLayout.refs layout.refs ∧
                              FibonacciModuleAnalysis.PreservesOtherClocks heap after ∧
                                LE.le.{0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (FibonacciModuleAnalysis.heapEventWork heap after)
                                    (Algo2Lean.Fibonacci.scaledPotential afterForest.counts))
                                  (HAdd.hAdd.{0, 0, 0}
                                    (Algo2Lean.Fibonacci.scaledPotential forest.counts) (20 : Nat)) := by
  sorry
