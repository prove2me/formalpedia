-- Prove2me | Theorems.Thm_BinaryModuleAnalysis_sift_up_loop
-- name    : BinaryModuleAnalysis.sift_up_loop
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:52:25.457995+00:00
-- url     : https://prove2.me/theorems/667c10eb-7af2-454e-a2a3-3d95bb068f98
-- title:
--   Indexed binary heap: sift-up correctness and running time
-- statement:
--   Let `heap` contain an allocated indexed min-heap object `queue` with valid storage layout, mutually inverse vertex/position arrays on its active prefix, and an index $0\le i<s$, where $s$ is the active size. Sifting upward terminates from any configuration at the corresponding loop location. It preserves that layout, indexing, membership, keys, unrelated storage, and every clock except heap comparisons and swaps. If `UpInvariant` holds initially, the final heap is ordered.
--
--   Writing $d(i)=\lfloor\log_2(i+1)\rfloor$, each of `heap_comparisons` and `heap_swaps` increases by at most $d(i)$. The public `CallFrom` conclusion permits an arbitrary caller stack. This local loop theorem is the proof boundary reused by insertion.
--
--   Costs count the named source ticks over mathematical integers and total integer-indexed sequences. They are not wall-clock time, bit complexity, or a count of every arithmetic operation, access, allocation, or compiler transition. Counters may start at arbitrary values; bounds refer to the increments during this call.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/indexed_heap.lean#L971-L1075

import Definitions.Def_Algo_indexed_heap_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem BinaryModuleAnalysis.sift_up_loop :
    ∀ (heap : Algo2LeanGenerated.Heap) (queue : Algo.indexed_heap.Algo2LeanGenerated.Ref_MinHeap)
      (layout : BinaryModuleAnalysis.Layout) (index : Int),
      layout.Valid heap queue →
        BinaryModuleAnalysis.Indexed (heap.read layout.vertices) (heap.read layout.positions)
            layout.size →
          LE.le.{0} (0 : Int) index →
            LT.lt.{0} index layout.size →
              Exists.{1} fun after =>
                (∀ (state : Algo.indexed_heap.Algo2LeanGenerated.Configuration),
                    BinaryModuleAnalysis.AtSiftUp state queue index →
                      Eq.{1} (Algo2LeanCore.Config.heap.{0, 0, 0} state) heap →
                        Algo.indexed_heap.MinHeap.sift_up.CallFrom state after ()) ∧
                  layout.Valid after queue ∧
                    BinaryModuleAnalysis.Indexed (after.read layout.vertices)
                        (after.read layout.positions) layout.size ∧
                      LE.le.{0} (after.clocks "heap_comparisons")
                          (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_comparisons")
                            (BinaryModuleAnalysis.depth index)) ∧
                        LE.le.{0} (after.clocks "heap_swaps")
                            (HAdd.hAdd.{0, 0, 0} (heap.clocks "heap_swaps")
                              (BinaryModuleAnalysis.depth index)) ∧
                          (BinaryModuleAnalysis.UpInvariant
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
