-- Prove2me | Theorems.Thm_ComposableDijkstraAnalysis_extraction_progress
-- name    : ComposableDijkstraAnalysis.extraction_progress
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-10T23:51:29.358716+00:00
-- url     : https://prove2.me/theorems/783e6347-ac04-4a78-8789-24518c9494a6
-- title:
--   Dijkstra: progress from an abstract priority-queue contract
-- statement:
--   Let `model` be a priority-queue model satisfying `Contracts`, with capacity at least the graph's vertex count. For any queue state and list of remaining vertices satisfying `LoopInvariant`, the next extraction satisfies `Execution.Progress` for the represented graph. This is the induction step used to prove the generic Dijkstra loop; it assumes the invariant, not an arbitrary malformed queue state.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/dijkstra.lean#L943-L1032

import Definitions.Def_Algo_dijkstra_dijkstra_Analysis

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem ComposableDijkstraAnalysis.extraction_progress :
    ∀ {dependencies : Algo.dijkstra.dijkstra.Dependencies} {client : ComposableDijkstraAnalysis.Client}
      (model : PriorityQueueAnalysis.Model dependencies.PriorityQueue client.queue client.protection),
      PriorityQueueAnalysis.Contracts model ComposableDijkstraAnalysis.reservedClocks →
        LE.le.{0} client.size model.capacity →
          ∀ (state : ComposableDijkstraAnalysis.QueueState model) (remaining : List.{0} Int),
            ComposableDijkstraAnalysis.LoopInvariant model state remaining →
              Algo2Lean.Dijkstra.Execution.Progress
                (ComposableDijkstraAnalysis.executionInterface model)
                (Algo2Lean.Dijkstra.representedEdges client.size client.adjacency) client.adjacency
                state remaining := by
  sorry
