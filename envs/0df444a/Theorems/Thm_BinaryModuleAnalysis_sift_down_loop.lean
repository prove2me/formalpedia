-- Prove2me | Theorems.Thm_BinaryModuleAnalysis_sift_down_loop
-- name    : BinaryModuleAnalysis.sift_down_loop
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:29.133315+00:00
-- url     : https://prove2.me/theorems/c0783e02-c026-4961-982f-4f8e7c394e6c
-- title:
--   Indexed binary heap: sift-down correctness and running time
-- statement:
--   Let a valid indexed heap have active size $s$ and start index $0\le i<s$. There is a terminating `MinHeap.sift_down.CallFrom` from each configuration at that loop location. It preserves storage validity, inverse indexing, keys and membership. Assuming `DownInvariant`, it restores heap order.
--
--   For $d(j)=\lfloor\log_2(j+1)\rfloor$ on nonnegative indices, comparisons increase by at most $2(d(s-1)-d(i))$ and swaps by at most $d(s-1)-d(i)$. All other arrays, non-array storage, and other clocks are preserved. The conclusion is independent of the caller stack.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/indexed_heap.lean#L1879-L2013

import Definitions.Def_Algo_indexed_heap_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem BinaryModuleAnalysis.sift_down_loop :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout) (index : Int),
      layout.Valid heap queue →
        BinaryModuleAnalysis.Indexed (heap.read layout.vertices) (heap.read layout.positions)
            layout.size →
          LE.le.{0} (0 : Int) index →
            LT.lt.{0} index layout.size →
              Exists.{1} fun after =>
                (∀ (state : Algo.indexed_heap.Algo2LeanGenerated.Configuration),
                    BinaryModuleAnalysis.AtSiftDown state queue index →
                      Eq.{1} (Algo2LeanCore.Config.heap.{0, 0, 0} state) heap →
                        Algo.indexed_heap.MinHeap.sift_down.CallFrom state after ()) ∧
                  layout.Valid after queue ∧
                    BinaryModuleAnalysis.Indexed (after.read layout.vertices)
                        (after.read layout.positions) layout.size ∧
                      LE.le.{0} (after.clocks "heap_comparisons")
                          (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_comparisons")
                            (HMul.hMul.{0, 0, 0} (2 : Nat)
                              (HSub.hSub.{0, 0, 0}
                                (BinaryModuleAnalysis.depth (HSub.hSub.{0, 0, 0} layout.size (1 : Int)))
                                (BinaryModuleAnalysis.depth index)))) ∧
                        LE.le.{0} (after.clocks "heap_swaps")
                            (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_swaps")
                              (HSub.hSub.{0, 0, 0}
                                (BinaryModuleAnalysis.depth (HSub.hSub.{0, 0, 0} layout.size (1 : Int)))
                                (BinaryModuleAnalysis.depth index))) ∧
                          (BinaryModuleAnalysis.DownInvariant
                                (fun position =>
                                  heap.read layout.keys (heap.read layout.vertices position))
                                layout.size index →
                              BinaryModuleAnalysis.Ordered
                                (fun position =>
                                  after.read layout.keys (after.read layout.vertices position))
                                layout.size) ∧
                            (∀ (ref : Algo2LeanGenerated.SeqRef),
                                Ne.{1} ref layout.vertices →
                                  Ne.{1} ref layout.positions →
                                    ∀ (position : Int),
                                      Eq.{1} (after.read ref position) (heap.read ref position)) ∧
                              (∀ (vertex : Int),
                                  LE.le.{0} (0 : Int) (after.read layout.positions vertex) ↔
                                    LE.le.{0} (0 : Int) (heap.read layout.positions vertex)) ∧
                                (∀ (name : String),
                                    Ne.{1} name "heap_comparisons" →
                                      Ne.{1} name "heap_swaps" →
                                        Eq.{1} (after.clocks name) (heap.clocks name)) ∧
                                  BinaryModuleAnalysis.OtherStoragePreserved heap after := by
  sorry
