-- Prove2me | Theorems.Thm_FibonacciDijkstraAnalysis_output_with_cost_correct
-- name    : FibonacciDijkstraAnalysis.output_with_cost_correct
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:08:54.10534+00:00
-- url     : https://prove2.me/theorems/0c7ed1f2-5158-4851-947a-70a53400a420
-- title:
--   Fibonacci Dijkstra: correctness and running time of every completed output
-- statement:
--   This result is part of the [Algo2Lean](https://www.algo2lean.com/) formalization series for *Introduction to Algorithms* (CLRS), fourth edition.
--
--   For a represented directed graph with nonnegative integer weights and an in-range source, every `dijkstra_fibonacci.ReturnsWithCost` output records the shortest distances and satisfies
--
--   $$T\leq 23(E+1)+\bigl(12(2\lfloor\log_2 V\rfloor+2)+3\bigr)V.$$
--
--   V is the vertex count, E is the number of adjacency entries, and T sums the thirteen chosen source-clock increments. Unreachable vertices have distance -1. This is the ordinary-value view of the reusable Call theorem; it does not duplicate the algorithm or heap proof. CLRS fourth edition, §22.3, Theorem 22.6 supplies the textbook correctness reference.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/dijkstra_fibonacci.lean#L201-L215

import Definitions.Def_Algo_dijkstra_dijkstra_fibonacci_Analysis
import Theorems.Thm_FibonacciDijkstraAnalysis_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciDijkstraAnalysis.output_with_cost_correct :
    ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.graph.Algo2LeanGenerated.Ref_Graph)
      (size source : Int) (heads : Algo2LeanGenerated.CollectionRef)
      (adjacency : Algo2Lean.Dijkstra.Adjacency) (output : Algo2LeanGenerated.Seq)
      (costs : Algo2LeanGenerated.Clocks),
      ComposableDijkstraAnalysis.GraphRep heap graph size heads adjacency →
        LE.le.{0} (0 : Int) source →
          LT.lt.{0} source size →
            Algo.dijkstra.dijkstra_fibonacci.dijkstra_fibonacci.ReturnsWithCost
                (Prod.mk.{0, 0} heap (Prod.mk.{0, 0} graph source)) output costs →
              Algo2Lean.Dijkstra.ShortestDistances (Algo2Lean.Dijkstra.representedEdges size adjacency)
                  source output ∧
                LE.le.{0} (FibonacciDijkstraAnalysis.clockWork costs)
                  (FibonacciDijkstraAnalysis.runtimeBound size adjacency) := by
  sorry
