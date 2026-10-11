-- Prove2me | Theorems.Thm_BinaryModuleAnalysis_insert_correct
-- name    : BinaryModuleAnalysis.insert_correct
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:53.814176+00:00
-- url     : https://prove2.me/theorems/5cf684d5-8ce5-44ea-919a-6fc8e3ee9b97
-- title:
--   Indexed binary heap: insertion correctness and running time
-- statement:
--   Assume `QueueRep heap queue layout`, and let integer vertex $v$ be absent (`positions[v] = -1`) with an arbitrary integer key $k$. There is a terminating `MinHeap.push_or_decrease.Call` that inserts $v$, increases the active size $s$ by one, restores the queue representation, and changes the key map only at $v$. An element is present afterward exactly when it was present before or equals $v$.
--
--   The call increments each of `heap_comparisons` and `heap_swaps` by at most $\lfloor\log_2(s+1)\rfloor$. Only the queue's three arrays and size field may change; unrelated storage and other clocks are preserved. This theorem covers the insertion branch, not decrease-key on an existing vertex.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/indexed_heap.lean#L1404-L1450

import Definitions.Def_Algo_indexed_heap_Analysis
import Theorems.Thm_BinaryModuleAnalysis_sift_up_loop

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem BinaryModuleAnalysis.insert_correct :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout),
      BinaryModuleAnalysis.QueueRep heap queue layout →
        ∀ (vertex key : Int),
          Eq.{1} (heap.read layout.positions vertex) (-1 : Int) →
            Exists.{1} fun after =>
              Algo.indexed_heap.MinHeap.push_or_decrease.Call heap
                  (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () ∧
                BinaryModuleAnalysis.QueueRep after queue
                    { vertices := layout.vertices, positions := layout.positions, keys := layout.keys,
                      size := HAdd.hAdd.{0, 0, 0} layout.size (1 : Int) } ∧
                  (∀ (value : Int),
                      LE.le.{0} (0 : Int) (after.read layout.positions value) ↔
                        Eq.{1} value vertex ∨ LE.le.{0} (0 : Int) (heap.read layout.positions value)) ∧
                    (∀ (value : Int),
                        Eq.{1} (after.read layout.keys value)
                          (ite.{1} (Eq.{1} value vertex) key (heap.read layout.keys value))) ∧
                      LE.le.{0} (heap.cost after "heap_comparisons")
                          (BinaryModuleAnalysis.depth layout.size) ∧
                        LE.le.{0} (heap.cost after "heap_swaps")
                            (BinaryModuleAnalysis.depth layout.size) ∧
                          (∀ (ref : Algo2LeanGenerated.SeqRef),
                              Ne.{1} ref layout.vertices →
                                Ne.{1} ref layout.positions →
                                  Ne.{1} ref layout.keys →
                                    ∀ (index : Int),
                                      Eq.{1} (after.read ref index) (heap.read ref index)) ∧
                            (∀ (name : String),
                                Ne.{1} name "heap_comparisons" →
                                  Ne.{1} name "heap_swaps" →
                                    Eq.{1} (after.clocks name) (heap.clocks name)) ∧
                              BinaryModuleAnalysis.OtherStoragePreserved
                                (Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_size heap queue
                                  (HAdd.hAdd.{0, 0, 0} layout.size (1 : Int)))
                                after := by
  sorry
