-- Prove2me | Theorems.Thm_FibonacciPrimAnalysis_correctness_and_running_time
-- name    : FibonacciPrimAnalysis.correctness_and_running_time
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T01:20:50.218978+00:00
-- url     : https://prove2.me/theorems/c9cf50d8-6575-4fc7-ac2e-2dd86a61cbb1
-- title:
--   CLRS — Chapter 21, §21.2: Prim with a Fibonacci Heap — Correctness and Running Time
-- statement:
--   Prove2Me mission category: **Textbook**.
--
--   ## Reusable minimum spanning tree algorithms
--
--   A minimum spanning tree connects a weighted network at minimum total edge cost.
--   When this routine is part of a larger algorithm, its caller also needs
--   termination, preservation of existing data, and a bound on the work performed.
--   These guarantees belong in a reusable contract, together with the returned
--   mathematical result.
--
--   This development follows *Introduction to Algorithms* (CLRS), fourth edition,
--   **Chapter 21, §21.2** for Prim and **Theorem 21.1 in §21.1** for safe edges.
--   The Fibonacci-heap analysis is in the publisher's online supplement, retained
--   Chapter 19, §§19.2–19.4, including Corollary 19.5. That supplement is distinct
--   from printed fourth-edition Chapter 19, which concerns disjoint sets.
--   [CLRS, fourth edition](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/);
--   [official Fibonacci-heap supplement](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/removed-from-3e.zip).
--
--   ## Graph, returned tree, and measured work
--
--   An **undirected weighted graph** has vertices `0, …, V−1` and finite adjacency
--   lists. Every edge occurs in both directions with the same integer weight.
--   Weights may be negative. Parallel edges retain separate occurrence identities,
--   and self-loops are permitted. Let `m` count undirected edge occurrences and `E`
--   count stored adjacency occurrences: the supplied graph constructor gives
--   `E = 2m`, including for self-loops. The root satisfies `0 ≤ root < V`, and the
--   main result assumes the graph is connected.
--
--   The output is a **parent sequence**, a mutable mathematical function from all
--   integer indices to integers. The root has parent `−1`; every other declared
--   vertex names its predecessor toward the root. A **minimum spanning tree** is
--   an acyclic selection of input edges connecting every declared vertex, with
--   minimum total weight among all competing spanning forests. The formal
--   `SpanningParents` predicate asserts this full property for the returned sequence.
--
--   A **heap** contains mutable sequences, objects, typed collections, and named
--   natural-number counters. A **Call contract** supplies a finite returning
--   execution in the generated semantics for every caller stack. Runtime `T` is
--   the increase in `clockWork`: each of seven Fibonacci-heap event counters and
--   six Prim bookkeeping counters is counted once. This measures explicit source
--   ticks, not elapsed time or integer bit complexity.
--
--   ## Formalization targets
--
--   The main target combines termination, minimum spanning tree correctness,
--   preservation of existing caller storage, fresh output allocation, and a bound
--   on the same execution's work. Its statement quantifies a single positive
--   constant before every graph, root, and initial heap:
--
--   $$
--   \exists C>0,\quad
--   T\le C\bigl(E+V(\lfloor\log_2 V\rfloor+1)\bigr)
--   \quad\text{for every valid connected input.}
--   $$
--
--   The constant is independent of the input and its initial counter values.
--   With `E = 2m`, this is the conventional $O(m+V\log V)$ bound. The logarithmic
--   unit covers a graph containing only the root. The supporting reusable result
--   retains the explicit estimate
--
--   $$
--   T\le 23(E+1)+\bigl(12(2\lfloor\log_2 V\rfloor+2)+3\bigr)V.
--   $$
--
--   `FibonacciPrimAnalysis.correctness_and_running_time` is the uniform-constant
--   main result. `FibonacciPrimAnalysis.summary` provides the explicit bound and
--   operation counts through `prim_fibonacci.Call`; `runtimeBound` and
--   `runtimeScale` name the two expressions. The ordinary-output consequences are
--   `output_exists` and `output_with_cost_correct`.
--
--   The component targets are the existing
--   [Fibonacci-heap correctness and amortized contract](https://prove2.me/theorems/6eb47bc3-01ce-4bb1-919c-bb626b4e49eb),
--   the pure safe-edge and parent-tree results, the queue-independent Prim call
--   contract, and their concrete composition. Invalid roots additionally return a
--   fresh all-`−1` sequence with zero ticks; no tree property is asserted for them.
--
--   ## What callers can reuse
--
--   The result lets a later algorithm invoke Prim on its current heap and receive
--   a valid new parent sequence, an unchanged graph representation, unchanged
--   preexisting sequences, objects, and typed collections, and a bound on the
--   additional work. Initial counters need not be zero. The generic Prim theorem
--   counts queue operations without depending on Fibonacci-heap internals; the
--   concrete theorem discharges its queue assumptions using the existing published
--   contract.
--
--   Prim's mathematical correctness and asymptotic complexity are established
--   textbook results. The [Algo2Lean](https://www.algo2lean.com/) development adds
--   proofs about this actual mutable source program, including termination and
--   storage preservation. Its complete Prim analysis has been checked locally
--   under Lean 4.33.1. The imported Fibonacci-heap contract already has an accepted
--   Prove2Me proof; the new Prim statements and proofs are prepared locally for
--   review. The graph definitions are shared with the Kruskal analysis. Later
--   clients can reuse these components without formalizing the data structure
--   again. Alternative queue implementations and improvements to the explicit
--   constants can retain the same mathematical specification.
--
--   ## Where the formalization is demanding
--
--   A minimum key alone does not establish that its parent pointer represents an
--   input edge, that the chosen edges connect all vertices, or that their total
--   weight is globally minimal. Those properties must remain connected to the
--   mutable sequences that the source updates, including when weights tie or are
--   negative.
--
--   A heap operation also changes shared mutable storage. Correct queue contents
--   alone do not guarantee preservation of the graph or unrelated caller data.
--   Moreover, some individual Fibonacci-heap operations are expensive despite
--   small amortized budgets. The contract must account for the same evolving
--   queue and counters across calls, rather than assume that every operation
--   starts with an empty heap. These obligations distinguish the complete
--   algorithm contract from a mathematical MST theorem or a count of queue calls.
--
--   ## Formalization scope and source
--
--   The `.algo` code closely follows the textbook pseudocode, with initialization,
--   minimum extraction, and adjacency relaxation expressed as source operations
--   and loops. It uses integer vertex handles and queues a vertex when first
--   discovered. A parent of `−1` denotes no discovered predecessor, so undiscovered
--   keys require no artificial infinity. The root is selected before any edge is
--   scanned. Relaxation compares an edge's weight directly; it does not add a
--   path distance.
--
--   Inputs are finite linked adjacency lists with bounded endpoints and signed,
--   unbounded integer weights. The theorem assumes a valid graph representation,
--   symmetric adjacency, connectedness, and an in-range root. It assumes neither
--   an existing successful transcript, a correct answer, nor an unverified
--   queue-runtime estimate. The conclusion compares the result with every
--   spanning forest. The whole-graph theorem does not apply to disconnected inputs.
--
--   The cost model counts the specified heap and Prim ticks. It does not count
--   every arithmetic operation, sequence access, allocation, or generated
--   transition. Constant-sequence and queue construction add no ticks; constructing
--   the input graph is outside the call. The imported queue API covers the
--   insert/decrease, minimum extraction, and emptiness operations used here; meld
--   and arbitrary deletion are outside this contract.
--
--   The compiler is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/),
--   whose immutable release commit is
--   [`0f79d5e`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76).
--   The Prim example and its proofs are versioned separately from this unchanged
--   compiler release. Compiler-output reproduction and Prove2Me import packaging
--   are separate checks: platform-adapted files need not have the raw generated
--   files' hashes. The compiler does not yet have a formal semantics-preservation
--   proof. The [Prim source and proof guide](https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/prim/README.md)
--   identifies the exact statements, definitions, and source files. The separate
--   example source commit is
--   [`d832a565`](https://github.com/lunjiah/algo2lean/tree/d832a5655d7cac6d032e728a4798128147b27922).
--
--   The project import root is `examples`. These are its three new source files.
--   The other imports are the existing `fibonacci_heap.algo` and
--   `dijkstra/priority_queue.algo`; the heap's independent source and analysis
--   belong to the linked published component.
--
--   ### `prim/graph.algo`
--
--   ```python
--   # An undirected graph with integer edge weights. Each edge is stored in both
--   # adjacency lists. Negative weights, parallel edges, and self-loops are allowed.
--
--   class Edge:
--       target: Int
--       weight: Int
--       next: Edge | None
--
--       def __init__(self, target: Int, weight: Int, next: Edge | None) -> None:
--           self.target = target
--           self.weight = weight
--           self.next = next
--
--
--   class Graph:
--       size: Int
--       heads: Seq[Edge | None]
--
--       def __init__(self, size: Int) -> None:
--           self.size = size
--           if size < 0:
--               self.size = 0
--           self.heads = const(None)
--
--       def add_edge(self, source: Int, target: Int, weight: Int) -> Bool:
--           if source < 0 or source >= self.size or target < 0 or target >= self.size:
--               return False
--           self.heads[source] = Edge(target, weight, self.heads[source])
--           self.heads[target] = Edge(source, weight, self.heads[target])
--           return True
--   ```
--
--   ### `prim/prim.algo`
--
--   ```python
--   from prim.graph import Graph, Edge
--   from dijkstra.priority_queue import PriorityQueue
--
--   # Prim's key is the cheapest edge from the growing tree to each vertex.
--   # parent stores the predecessor; -1 means no predecessor has been assigned.
--   # Vertices enter the queue when first reached, so infinity need not be encoded.
--   # The caller supplies an empty queue, zero keys and selected flags, and parents
--   # filled with -1. The root retains parent -1. Queue and client storage are disjoint.
--
--   def scan_edges(queue: PriorityQueue, key: Seq, parent: Seq, selected: Seq,
--                  vertex: Int, edge: Edge | None) -> None:
--       # @scan
--       while edge is not None:
--           tick("edges")
--           target = edge.target
--           if selected[target] == 0:
--               weight = edge.weight
--               if parent[target] < 0 or weight < key[target]:
--                   # @improve
--                   key[target] = weight
--                   parent[target] = vertex
--                   tick("queue_updates")
--                   queue.push_or_decrease(target, weight)
--                   tick("improvements")
--           edge = edge.next
--
--
--   def prim(graph: Graph, root: Int, queue: PriorityQueue,
--            key: Seq, parent: Seq, selected: Seq) -> Seq:
--       key[root] = 0
--       tick("queue_updates")
--       queue.push_or_decrease(root, 0)
--       tick("queue_empty_checks")
--       # @extract
--       while not queue.is_empty():
--           tick("queue_pops")
--           vertex = queue.pop_min()
--           selected[vertex] = 1
--           tick("settlements")
--           scan_edges(queue, key, parent, selected, vertex, graph.heads[vertex])
--           tick("queue_empty_checks")
--       return parent
--   ```
--
--   ### `prim/prim_fibonacci.algo`
--
--   ```python
--   from prim.graph import Graph
--   from fibonacci_heap import FibonacciHeap
--   from prim.prim import prim as grow_tree
--
--   # On a connected graph, the returned predecessors describe a minimum spanning
--   # tree rooted at root. The root has predecessor -1. An invalid root returns -1
--   # everywhere without constructing a queue.
--   def prim_fibonacci(graph: Graph, root: Int) -> Seq:
--       parent = const(-1)
--       if root < 0 or root >= graph.size:
--           return parent
--       key = const(0)
--       selected = const(0)
--       queue = FibonacciHeap()
--       return grow_tree(graph, root, queue, key, parent, selected)
--   ```
--
--   ## Selected references
--
--   - Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
--     *Introduction to Algorithms*, fourth edition, MIT Press, 2022, Chapter 21,
--     §§21.1–21.2, Theorem 21.1.
--     [Publisher](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/).
--   - The same authors, *Fibonacci Heaps*, official online supplement to the fourth
--     edition, retained Chapter 19 of the third edition, MIT Press, 2009/2022,
--     §§19.2–19.4, Corollary 19.5.
--     [Publisher's supplement](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/removed-from-3e.zip).
--   - [Algo2Lean](https://www.algo2lean.com/), version 0.1.4, Lean-targeting compiler and source examples.
--     [Compiler](https://www.algo2lean.com/versions/v0.1.4/) and
--     [source repository](https://github.com/lunjiah/algo2lean).
--   - `FibonacciQueueAnalysis.contracts`, independently verified Fibonacci-heap
--     queue behavior, preservation, and amortized work.
--     [Published Prove2Me theorem](https://prove2.me/theorems/6eb47bc3-01ce-4bb1-919c-bb626b4e49eb).
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/d832a5655d7cac6d032e728a4798128147b27922/examples/analysis/prim/prim_fibonacci.lean#L353-L374

import Definitions.Def_Algo_prim_prim_fibonacci_Analysis
import Theorems.Thm_FibonacciPrimAnalysis_summary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciPrimAnalysis.correctness_and_running_time :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
        ∀ (heap : Algo2LeanGenerated.Heap) (graph : Algo.prim.graph.Algo2LeanGenerated.Ref_Graph)
          (size root : Int) (heads : Algo2LeanGenerated.CollectionRef)
          (adjacency : Algo2Lean.Dijkstra.Adjacency),
          PrimGraph.GraphRep heap graph size heads adjacency →
            LE.le.{0} (0 : Int) root →
              LT.lt.{0} root size →
                PrimGraph.Symmetric size adjacency →
                  Algo2Lean.Kruskal.ConnectedOn size.toNat (PrimGraph.inputEdges size adjacency) →
                    Exists.{1} fun after =>
                      Algo.prim.prim_fibonacci.prim_fibonacci.Call heap (Prod.mk.{0, 0} graph root)
                          after heap.nextRef ∧
                        PrimGraph.GraphRep after graph size heads adjacency ∧
                          PrimAnalysis.MinimumSpanningParents size adjacency root
                              (after.read heap.nextRef) ∧
                            LE.le.{0} (FibonacciPrimAnalysis.clockWork (heap.cost after))
                                (HMul.hMul.{0, 0, 0} C
                                  (FibonacciPrimAnalysis.runtimeScale size adjacency)) ∧
                              LT.lt.{0} heap.nextRef after.nextRef ∧
                                heap.Footprint after List.nil.{0} List.nil.{0} List.nil.{0} := by
  sorry
