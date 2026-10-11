-- Prove2me | Theorems.Thm_FibonacciModuleAnalysis_QueueRep_update
-- name    : FibonacciModuleAnalysis.QueueRep.update
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:02:05.30028+00:00
-- url     : https://prove2.me/theorems/e5d47cda-b44b-4922-b095-a30b227482f3
-- title:
--   Fibonacci heap: reusable push-or-decrease correctness and running time
-- statement:
--   For a represented queue, a nonnegative handle v, and a key k strictly below any existing key at v, push_or_decrease terminates and updates exactly that binding. The final Call preserves the representation, storage outside the queue, the same layout references, and unrelated clocks.
--
--   For measured heap events T and scaled potential Ψ,
--
--   $$T+\Psi(\mathrm{after})\leq\Psi(\mathrm{before})+20.$$
--
--   The key condition is vacuous for a new handle; it is a strict-decrease condition for an existing handle. This is a reusable data-structure contract, independent of a graph algorithm.
--
--   ## Algorithm source
--
--   Project import root: `examples`. Entry file: `fibonacci_heap.algo`.
--
--   ### `fibonacci_heap.algo`
--
--   ```python
--   # An indexed Fibonacci heap. Nonnegative vertex identifiers are stable handles.
--   # The active forest uses circular doubly linked sibling rings. A -1 parent
--   # means root; a -1 child/minimum means empty. Present and mark entries are 0/1.
--   # A nonroot is marked after losing one child and cut after losing another.
--   # const allocates a constant-valued mathematical sequence. Allocation has no
--   # heap-event tick; the cost model counts the explicit ticks below. Consolidation
--   # reuses its table and clears every visited bucket between public operations.
--   # The operations follow the CLRS Fibonacci-heap supplement, using integer
--   # handles in place of node pointers and an iterative cascading cut.
--
--   class FibonacciHeap:
--       keys: Seq
--       parents: Seq
--       children: Seq
--       left: Seq
--       right: Seq
--       degrees: Seq
--       marks: Seq
--       present: Seq
--       table: Seq
--       minimum: Int
--       size: Int
--
--       def __init__(self) -> None:
--           self.keys = const(0)
--           self.parents = const(-1)
--           self.children = const(-1)
--           self.left = const(0)
--           self.right = const(0)
--           self.degrees = const(0)
--           self.marks = const(0)
--           self.present = const(0)
--           self.table = const(-1)
--           self.minimum = -1
--           self.size = 0
--
--       # Internal ring helpers receive a present vertex, detached or in its ring.
--       def remove_from_ring(self, vertex: Int) -> None:
--           before = self.left[vertex]
--           after = self.right[vertex]
--           self.right[before] = after
--           self.left[after] = before
--           self.left[vertex] = vertex
--           self.right[vertex] = vertex
--
--       def add_root(self, vertex: Int) -> None:
--           self.parents[vertex] = -1
--           self.marks[vertex] = 0
--           if self.minimum < 0:
--               self.left[vertex] = vertex
--               self.right[vertex] = vertex
--               self.minimum = vertex
--           else:
--               first = self.minimum
--               after = self.right[first]
--               self.left[vertex] = first
--               self.right[vertex] = after
--               self.right[first] = vertex
--               self.left[after] = vertex
--               tick("heap_comparisons")
--               if self.keys[vertex] < self.keys[first]:
--                   self.minimum = vertex
--
--       def link(self, child: Int, parent: Int) -> None:
--           # FIB-HEAP-LINK: both roots have already been detached from the root ring.
--           # @link_child
--           self.parents[child] = parent
--           self.marks[child] = 0
--           first = self.children[parent]
--           if first < 0:
--               self.left[child] = child
--               self.right[child] = child
--           else:
--               before = self.left[first]
--               self.left[child] = before
--               self.right[child] = first
--               self.right[before] = child
--               self.left[first] = child
--           # Children are traversed from most recently linked to oldest.
--           self.children[parent] = child
--           self.degrees[parent] = self.degrees[parent] + 1
--           tick("heap_links")
--
--       def consolidate(self) -> None:
--           table = self.table
--           maximum_degree = -1
--           # Remove roots one at a time. Table entries are detached roots, so
--           # linking a collision cannot invalidate traversal of the remaining ring.
--           # @consume_roots
--           while self.minimum >= 0:
--               vertex = self.minimum
--               if self.right[vertex] == vertex:
--                   self.minimum = -1
--               else:
--                   self.minimum = self.right[vertex]
--               self.remove_from_ring(vertex)
--               tick("heap_root_scans")
--               degree = self.degrees[vertex]
--               # @equal_degree
--               while table[degree] >= 0:
--                   other = table[degree]
--                   table[degree] = -1
--                   tick("heap_comparisons")
--                   if self.keys[other] < self.keys[vertex]:
--                       temporary = vertex
--                       vertex = other
--                       other = temporary
--                   self.link(other, vertex)
--                   degree += 1
--               table[degree] = vertex
--               if degree > maximum_degree:
--                   maximum_degree = degree
--           degree = 0
--           # @rebuild_roots
--           while degree <= maximum_degree:
--               tick("heap_degree_scans")
--               vertex = table[degree]
--               table[degree] = -1
--               if vertex >= 0:
--                   self.add_root(vertex)
--               degree += 1
--
--       def cut(self, vertex: Int, parent: Int) -> None:
--           if self.children[parent] == vertex:
--               if self.right[vertex] == vertex:
--                   self.children[parent] = -1
--               else:
--                   self.children[parent] = self.right[vertex]
--           self.degrees[parent] = self.degrees[parent] - 1
--           self.remove_from_ring(vertex)
--           # @cut_to_root
--           self.add_root(vertex)
--           tick("heap_cuts")
--
--       def cascading_cut(self, vertex: Int) -> None:
--           # CASCADING-CUT: follow parents until a root or the first unmarked node.
--           parent = self.parents[vertex]
--           # @cascade
--           while parent >= 0:
--               if self.marks[vertex] == 0:
--                   self.marks[vertex] = 1
--                   return
--               self.cut(vertex, parent)
--               vertex = parent
--               parent = self.parents[vertex]
--
--       def push_or_decrease(self, vertex: Int, key: Int) -> None:
--           # FIB-HEAP-INSERT for an absent handle; FIB-HEAP-DECREASE-KEY otherwise.
--           # This combined API ignores equal or larger keys for a present handle.
--           tick("heap_operations")
--           if self.present[vertex] == 0:
--               self.keys[vertex] = key
--               self.children[vertex] = -1
--               self.degrees[vertex] = 0
--               self.present[vertex] = 1
--               self.size += 1
--               # @insert_root
--               self.add_root(vertex)
--               return
--           tick("heap_comparisons")
--           if key >= self.keys[vertex]:
--               return
--           self.keys[vertex] = key
--           parent = self.parents[vertex]
--           if parent >= 0:
--               tick("heap_comparisons")
--               if key < self.keys[parent]:
--                   self.cut(vertex, parent)
--                   self.cascading_cut(parent)
--           tick("heap_comparisons")
--           if self.keys[vertex] < self.keys[self.minimum]:
--               self.minimum = vertex
--
--       def pop_min(self) -> Int:
--           # FIB-HEAP-EXTRACT-MIN, returning a handle or -1 for an empty heap.
--           tick("heap_operations")
--           vertex = self.minimum
--           if vertex < 0:
--               return -1
--           # @promote_children
--           while self.children[vertex] >= 0:
--               child = self.children[vertex]
--               if self.right[child] == child:
--                   self.children[vertex] = -1
--               else:
--                   self.children[vertex] = self.right[child]
--               self.degrees[vertex] = self.degrees[vertex] - 1
--               self.remove_from_ring(child)
--               self.add_root(child)
--               tick("heap_promotions")
--           after = self.right[vertex]
--           self.remove_from_ring(vertex)
--           self.present[vertex] = 0
--           self.size -= 1
--           if after == vertex:
--               self.minimum = -1
--           else:
--               self.minimum = after
--               self.consolidate()
--           return vertex
--
--       def is_empty(self) -> Bool:
--           return self.size <= 0
--   ```
--
--   ### `dijkstra/priority_queue.algo`
--
--   ```python
--   from algo2lean import Interface
--
--   # Behavior, framing, and cost laws live in analysis/priority_queue.lean.
--   # Construction is separate: clients receive an initialized queue.
--   class PriorityQueue(Interface):
--       def push_or_decrease(self, vertex: Int, key: Int) -> None: ...
--       def pop_min(self) -> Int: ...
--       def is_empty(self) -> Bool: ...
--   ```
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/analysis/dijkstra/support/fibonacci_heap.lean#L4994-L5020

import Definitions.Def_Algo_dijkstra_support_fibonacci_heap_Analysis
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_insert
import Theorems.Thm_FibonacciModuleAnalysis_QueueRep_decrease

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem FibonacciModuleAnalysis.QueueRep.update :
    ∀ {heap : Algo2LeanGenerated.Heap}
      {queue : Algo.fibonacci_heap.Algo2LeanGenerated.Ref_FibonacciHeap}
      {layout : FibonacciModuleAnalysis.Layout} {forest : Algo2Lean.Fibonacci.Forest},
      FibonacciModuleAnalysis.QueueRep heap queue layout forest →
        ∀ (vertex key : Int),
          LE.le.{0} (0 : Int) vertex →
            (∀ (old : Int),
                Membership.mem.{0, 0} forest.entries (Prod.mk.{0, 0} vertex old) → LT.lt.{0} key old) →
              Exists.{1} fun after =>
                Exists.{1} fun finalLayout =>
                  Exists.{1} fun afterForest =>
                    Algo.fibonacci_heap.FibonacciHeap.push_or_decrease.Call heap
                        (Prod.mk.{0, 0} queue (Prod.mk.{0, 0} vertex key)) after () ∧
                      FibonacciModuleAnalysis.QueueRep after queue finalLayout afterForest ∧
                        (∀ (v k : Int),
                            Membership.mem.{0, 0} afterForest.entries (Prod.mk.{0, 0} v k) ↔
                              Eq.{1} v vertex ∧ Eq.{1} k key ∨
                                Ne.{1} v vertex ∧
                                  Membership.mem.{0, 0} forest.entries (Prod.mk.{0, 0} v k)) ∧
                          heap.Modifies after layout.refs (List.cons.{0} queue List.nil.{0}) ∧
                            Eq.{1} finalLayout.refs layout.refs ∧
                              FibonacciModuleAnalysis.PreservesOtherClocks heap after ∧
                                LE.le.{0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (FibonacciModuleAnalysis.heapEventWork heap after)
                                    (Algo2Lean.Fibonacci.scaledPotential afterForest.counts))
                                  (HAdd.hAdd.{0, 0, 0}
                                    (Algo2Lean.Fibonacci.scaledPotential forest.counts) (20 : Nat)) := by
  sorry
