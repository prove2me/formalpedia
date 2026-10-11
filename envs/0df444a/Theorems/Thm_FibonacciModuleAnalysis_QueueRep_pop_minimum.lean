-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_QueueRep_pop_minimum
-- name    : FibonacciModuleAnalysis.QueueRep.pop_minimum
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:02:37.947997+00:00
-- url     : https://prove2.me/theorems/a77de1fe-923b-484d-a0cd-3b1559cd49d2
-- title:
--   Fibonacci heap: minimum extraction correctness and amortized running time
-- statement:
--   A represented nonempty queue admits a terminating pop_min Call satisfying `PopContract`: it removes a minimum binding, preserves the representation of the remaining queue, and carries the before/after potential for the same call. Only the sequences in `layout.refs` and the queue object may change; all other sequence/object contents, all typed collections, allocation frontiers and object class tags are preserved. For n initial entries, measured heap work T and scaled potential Ψ = 4(roots + 2 marks), the contract bounds
--
--   $$T+\Psi(\mathrm{after})\leq\Psi(\mathrm{before})+12(2\lfloor\log_2 n\rfloor+2).$$
--
--   The bound concerns the seven named heap clocks. It is amortized, so a single extraction need not itself have logarithmic actual work.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L5283-L5348

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_pop_effect_summary
import Theorems.Thm_FibonacciModuleAnalysis_extract_from_pending
import Theorems.Thm_Algo2Lean_Fibonacci_Represented_delete_minimum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.QueueRep.pop_minimum :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        Ne.{1} forest List.nil.{0} →
          Exists.{1} fun after =>
            Exists.{1} fun finalLayout =>
              Exists.{1} fun afterForest =>
                FibonacciModuleAnalysis.PopContract heap queue layout forest after finalLayout
                  afterForest := by
  sorry
