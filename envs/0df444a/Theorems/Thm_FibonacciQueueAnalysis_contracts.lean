-- Prove2me | Theorems.Thm_FibonacciQueueAnalysis_contracts
-- name    : FibonacciQueueAnalysis.contracts
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:04:16.147988+00:00
-- url     : https://prove2.me/theorems/6eb47bc3-01ce-4bb1-919c-bb626b4e49eb
-- title:
--   Fibonacci heap: instantiate the reusable queue and running-time interface
-- statement:
--   The verified Fibonacci implementation satisfies the generic `PriorityQueueAnalysis.Contracts` through a supplied code bridge. The protected object classes must exclude the mutable Fibonacci-heap class, and reserved client clocks must be disjoint from heap clocks. Each method contract applies to a state satisfying the model's `Rep`: the queue is represented with handles within capacity, protected client sequences are disjoint from its private sequence references, and the private queue object/sequences and client work sequences are fresh relative to the saved caller snapshot. That snapshot's allocated contents are retained by the representation. Queue calls also preserve the contents of listed protected sequences and typed collections, and of objects whose class is listed as protected, when allocated before the call. Existing object and collection type tags remain unchanged. These conditions do not assert that arbitrary storage aliased with the queue is preserved. Each operation's measured work and potential are attached to the same concrete execution, permitting the generic Dijkstra proof to use the heap without unfolding its transitions.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_queue.lean#L142-L204

import Definitions.Def_Algo_dijkstra_support_fibonacci_queue_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_update
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_pop_minimum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciQueueAnalysis.contracts :
    ∀ (code : Algo.dijkstra.priority_queue.PriorityQueue.Code)
      (bridge : FibonacciQueueAnalysis.Bridge code) (queue : Algo2LeanGenerated.ObjectRef)
      (protection : PriorityQueueAnalysis.Protected) (capacity : Int) (reserved : List.{0} String),
      ¬Membership.mem.{0, 0} protection.objectClasses "fibonacci_heap.FibonacciHeap" →
        (∀ (name : String),
            Membership.mem.{0, 0} reserved name →
              ¬Membership.mem.{0, 0} FibonacciModuleAnalysis.heapClocks name) →
          PriorityQueueAnalysis.Contracts
            (FibonacciQueueAnalysis.model code bridge queue protection capacity) reserved := by
  sorry
