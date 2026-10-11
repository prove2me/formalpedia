-- Prove2me | Theorems.Thm_BinaryModuleAnalysis_pop_multiple_correct
-- name    : BinaryModuleAnalysis.pop_multiple_correct
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:59.65221+00:00
-- url     : https://prove2.me/theorems/f0b071b9-9de1-4a3f-b19f-f84e8611f877
-- title:
--   Indexed binary heap: minimum extraction and logarithmic running time
-- statement:
--   For a represented indexed min-heap of size $s>1$, `MinHeap.pop_min.Call` terminates and returns its root vertex. The `Extracted` postcondition proves minimum-key correctness, removal of exactly this vertex, preservation of every key, restoration of a queue of size $s-1$, and preservation of unrelated storage and clocks.
--
--   With $d(j)=\lfloor\log_2(j+1)\rfloor$, comparisons increase by at most $2d(s-2)$ and swaps by at most $d(s-2)+1$. Equal and negative priorities are permitted. This reusable extraction contract is independent of the sorter and of Kruskal.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/indexed_heap.lean#L2328-L2370

import Definitions.Def_Algo_indexed_heap_Analysis
import Theorems.Thm_BinaryModuleAnalysis_sift_down_loop

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem BinaryModuleAnalysis.pop_multiple_correct :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout),
      BinaryModuleAnalysis.QueueRep heap queue layout →
        LT.lt.{0} (1 : Int) layout.size →
          Exists.{1} fun after =>
            Algo.indexed_heap.MinHeap.pop_min.Call heap queue after
                (heap.read layout.vertices (0 : Int)) ∧
              BinaryModuleAnalysis.Extracted heap after queue layout
                (heap.read layout.vertices (0 : Int)) := by
  sorry
