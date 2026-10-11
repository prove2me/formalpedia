-- Prove2me | Theorems.Thm_FibonacciPrimAnalysis_output_with_cost_correct
-- name    : FibonacciPrimAnalysis.output_with_cost_correct
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T01:20:23.536091+00:00
-- url     : https://prove2.me/theorems/1586c2c1-94f1-44b6-af5c-0cc117642506
-- title:
--   Prim with a Fibonacci Heap: correctness and runtime of every completed output
-- statement:
--   For a represented connected undirected graph with signed integer weights and a valid root, every prim_fibonacci.ReturnsWithCost output is a minimum spanning parent sequence and satisfies T ≤ 23(E+1) + (12(2⌊log₂ V⌋+2)+3)V. E counts stored adjacency occurrences and T sums the specified thirteen source-clock increments. This ordinary-output consequence uses the reusable Call theorem and deterministic execution; it does not repeat the graph or heap proof. CLRS fourth edition, Chapter 21, §21.2.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/prim_fibonacci.lean#L333-L350

import Definitions.Def_Algo_prim_prim_fibonacci_Analysis
import Theorems.Thm_FibonacciPrimAnalysis_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciPrimAnalysis.output_with_cost_correct :
    ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.prim.graph.Algo2LeanGenerated.Ref_Graph)
      (size root : Int) (heads : Algo2LeanGenerated.CollectionRef)
      (adjacency : Algo2Lean.Dijkstra.Adjacency) (output : Algo2LeanGenerated.Seq)
      (costs : Algo2LeanGenerated.Clocks),
      PrimGraph.GraphRep heap graph size heads adjacency →
        LE.le.{0} (0 : Int) root →
          LT.lt.{0} root size →
            PrimGraph.Symmetric size adjacency →
              Algo2Lean.Kruskal.ConnectedOn size.toNat (PrimGraph.inputEdges size adjacency) →
                Algo.prim.prim_fibonacci.prim_fibonacci.ReturnsWithCost
                    (Prod.mk.{0, 0} heap (Prod.mk.{0, 0} graph root)) output costs →
                  PrimAnalysis.MinimumSpanningParents size adjacency root output ∧
                    LE.le.{0} (FibonacciPrimAnalysis.clockWork costs)
                      (FibonacciPrimAnalysis.runtimeBound size adjacency) := by
  sorry
