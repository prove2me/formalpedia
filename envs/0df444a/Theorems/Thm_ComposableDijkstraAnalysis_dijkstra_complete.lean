-- Prove2me | Theorems.Thm_ComposableDijkstraAnalysis_dijkstra_complete
-- name    : ComposableDijkstraAnalysis.dijkstra_complete
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:53:49.933514+00:00
-- url     : https://prove2.me/theorems/983ad8a0-2b70-4908-8dcb-212a2b13595b
-- title:
--   Dijkstra: correctness and running time for a reusable queue interface
-- statement:
--   For a represented graph with nonnegative integer weights, a valid source, a represented empty queue with sufficient capacity, and distinct allocated distance/settled sequences initially equal to -1/0, the compiled generic Dijkstra call terminates and computes shortest distances. The queue must satisfy the independently stated operation contracts. The same call preserves the graph and every location allocated in the saved `client.caller` snapshot, returns the supplied distance sequence, and satisfies `OperationCounts`. The distance and settled work sequences themselves may change.
--
--   With initial queue potential Φ, update budget U, pop budget P, V vertices and E adjacency entries, its backend-weighted work W obeys
--
--   $$W\leq\Phi+U(E+1)+PV.$$
--
--   These are named source events; they do not count all machine instructions. Concrete queue contracts discharge the hypotheses without repeating this graph proof.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/dijkstra.lean#L1053-L1159

import Definitions.Def_Algo_dijkstra_dijkstra_Analysis
import Theorems.Thm_ComposableDijkstraAnalysis_extraction_progress

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem ComposableDijkstraAnalysis.dijkstra_complete :
    ∀ {dependencies : Algo.dijkstra.dijkstra.Dependencies} {client : ComposableDijkstraAnalysis.Client}
      (model : PriorityQueueAnalysis.Model dependencies.PriorityQueue client.queue client.protection),
      PriorityQueueAnalysis.Contracts model ComposableDijkstraAnalysis.reservedClocks →
        LE.le.{0} client.size model.capacity →
          ∀ (before : ComposableDijkstraAnalysis.QueueState model) (source : Int),
            ComposableDijkstraAnalysis.Storage model before →
              Eq.{1} (ComposableDijkstraAnalysis.QueueState.entries model before) List.nil.{0} →
                (Eq.{1} (before.heap.read client.distance) fun x => (-1 : Int)) →
                  (Eq.{1} (before.heap.read client.settled) fun x => (0 : Int)) →
                    LE.le.{0} (0 : Int) source →
                      LT.lt.{0} source client.size →
                        Exists.{1} fun after =>
                          Algo.dijkstra.dijkstra.dijkstra.Call dependencies before.heap
                              (Prod.mk.{0, 0} client.graph
                                (Prod.mk.{0, 0} source
                                  (Prod.mk.{0, 0} client.queue
                                    (Prod.mk.{0, 0} client.distance client.settled))))
                              after client.distance ∧
                            ComposableDijkstraAnalysis.GraphRep after client.graph client.size
                                client.heads client.adjacency ∧
                              Algo2Lean.Dijkstra.ShortestDistances
                                  (Algo2Lean.Dijkstra.representedEdges client.size client.adjacency)
                                  source (after.read client.distance) ∧
                                ComposableDijkstraAnalysis.OperationCounts before.heap after
                                    client.size.toNat
                                    (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                      (Algo2Lean.Dijkstra.vertexRange client.size)) ∧
                                  LE.le.{0} (ComposableDijkstraAnalysis.work model before.heap after)
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (ComposableDijkstraAnalysis.QueueState.potential model before)
                                          (HMul.hMul.{0, 0, 0} model.updateBudget
                                            (HAdd.hAdd.{0, 0, 0}
                                              (Algo2Lean.Dijkstra.edgeBudget client.adjacency
                                                (Algo2Lean.Dijkstra.vertexRange client.size))
                                              (1 : Nat))))
                                        (HMul.hMul.{0, 0, 0} model.popBudget client.size.toNat)) ∧
                                    LT.lt.{0} client.distance after.nextRef ∧
                                      client.caller.Footprint after List.nil.{0} List.nil.{0}
                                        List.nil.{0} := by
  sorry
