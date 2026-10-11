-- Prove2me | Theorems.Thm_FibonacciPrimAnalysis_summary
-- name    : FibonacciPrimAnalysis.summary
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T01:17:37.255866+00:00
-- url     : https://prove2.me/theorems/48b87baa-9bc6-47d0-a721-26e5c4d4c958
-- title:
--   Prim with a Fibonacci Heap: reusable correctness and explicit runtime contract
-- statement:
--   For every represented connected undirected graph with signed integer weights and a root in range, the actual compiled prim_fibonacci call terminates, allocates a fresh parent sequence describing a minimum spanning tree, preserves the graph and every preexisting caller location, and satisfies the operation counts and bound T ≤ 23(E+1) + (12(2⌊log₂ V⌋+2)+3)V. V counts vertices, E counts adjacency occurrences, and T sums seven heap clocks and six Prim clocks once each. Counter values need not start at zero. The result reuses the existing published FibonacciQueueAnalysis.contracts theorem and the queue-independent PrimAnalysis.prim_complete theorem; it does not assume a successful transcript or correct output. CLRS fourth edition, Chapter 21, §21.2.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/prim_fibonacci.lean#L240-L299

import Definitions.Def_Algo_prim_prim_fibonacci_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_new_heap_representation
import Theorems.Thm_FibonacciQueueAnalysis_contracts
import Theorems.Thm_PrimAnalysis_prim_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciPrimAnalysis.summary :
    ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.prim.graph.Algo2LeanGenerated.Ref_Graph)
      (size root : Int) (heads : Algo2LeanGenerated.CollectionRef)
      (adjacency : Algo2Lean.Dijkstra.Adjacency),
      PrimGraph.GraphRep heap graph size heads adjacency →
        LE.le.{0} (0 : Int) root →
          LT.lt.{0} root size →
            PrimGraph.Symmetric size adjacency →
              Algo2Lean.Kruskal.ConnectedOn size.toNat (PrimGraph.inputEdges size adjacency) →
                Exists.{1} fun after =>
                  Algo.prim.prim_fibonacci.prim_fibonacci.Call heap (Prod.mk.{0, 0} graph root) after
                      heap.nextRef ∧
                    PrimGraph.GraphRep after graph size heads adjacency ∧
                      PrimAnalysis.MinimumSpanningParents size adjacency root
                          (after.read heap.nextRef) ∧
                        PrimAnalysis.OperationCounts heap after size.toNat
                            (Algo2Lean.Dijkstra.edgeBudget adjacency
                              (Algo2Lean.Dijkstra.vertexRange size)) ∧
                          LE.le.{0} (FibonacciPrimAnalysis.clockWork (heap.cost after))
                              (FibonacciPrimAnalysis.runtimeBound size adjacency) ∧
                            LT.lt.{0} heap.nextRef after.nextRef ∧
                              heap.Footprint after List.nil.{0} List.nil.{0} List.nil.{0} := by
  sorry
