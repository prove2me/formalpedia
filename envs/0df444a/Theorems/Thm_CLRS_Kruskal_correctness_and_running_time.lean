-- Prove2me | Theorems.Thm_CLRS_Kruskal_correctness_and_running_time
-- name    : CLRS.Kruskal.correctness_and_running_time
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:08:13.455131+00:00
-- url     : https://prove2.me/theorems/e793cbba-0d75-4733-9c90-dc210e49c695
-- title:
--   CLRS Chapter 21, §21.2: Kruskal — Correctness and Inverse-Ackermann Running Time
-- statement:
--   This is a capstone of the [Algo2Lean](https://www.algo2lean.com/) formalization series for *Introduction to Algorithms* (CLRS), fourth edition: Chapter 21, §21.2 (Kruskal), using the safe-edge principle of Theorem 21.1 (§21.1); union by rank and full path compression use Chapter 19, §§19.3–19.4, Theorem 19.14.
--
--   There exists a universal positive constant C such that every well-formed graph input admits one terminating compiled Call returning minimum-spanning-forest flags, with
--
--   $$T \le C\bigl(V+1+E(\lfloor\log_2(E+1)\rfloor+\alpha(V)+1)\bigr).$$
--
--   The positive constant is quantified before every heap, graph and input; it cannot be chosen separately for each execution. The earlier exact-constant theorem remains available as an auxiliary reusable result.
--
--   Thus the chosen source clocks have growth O(V + E log(E+1) + E alpha(V)). The same final heap preserves caller storage, allocates the flag sequence freshly and records clock increments from arbitrary initial counters. The bound includes edge sorting and union-find initialization, but does not count all machine operations. The inverse-Ackermann operation bounds are proved once in the data-structure layer and reused here.
--
--   The `.algo` code closely follows the textbook pseudocode: initialize the
--   empty selection and singleton components, sort edges by weight, then compare
--   endpoint representatives before selecting an edge and joining its components.
--   Edge identifiers and flags represent sets, the constructor performs the
--   make-set loop, and an independently verified sorter supplies the abstract
--   sorting operation. Full path compression and union by rank remain in the
--   independently analyzed data structure; the runtime includes the explicit
--   finds and the finds performed inside accepted unions.
--
--   ## Algorithm source
--
--   Project import root: `examples/kruskal`. Entry file: `kruskal.algo`.
--
--   ### `union_find.algo`
--
--   ```python
--   # Disjoint sets over the integer elements 0, ..., size - 1.
--   # Each root names one component. Union by rank bounds parent paths, and
--   # find compresses every visited path directly to its root.
--   # Clients must pass in-range elements. The representation is independent
--   # of graphs, edge weights, or any particular client algorithm.
--
--   class UnionFind:
--       parent: Seq
--       rank: Seq
--       size: Int
--
--       def __init__(self, size: Int) -> None:
--           # Batch the CLRS MAKE-SET operation for all elements in [0, size).
--           self.parent = const(0)
--           self.rank = const(0)
--           self.size = size
--           vertex = 0
--           tick("uf_init")
--           # @initialize
--           while vertex < size:
--               self.parent[vertex] = vertex
--               vertex += 1
--               tick("uf_init")
--
--       def find(self, vertex: Int) -> Int:
--           # CLRS FIND-SET: recursion finds the root, then rewrites every parent
--           # along the return path. This is full path compression, not path halving.
--           parent = self.parent
--           tick("uf_find")
--           # @follow
--           if parent[vertex] == vertex:
--               return vertex
--           root = self.find(parent[vertex])
--           # @compress
--           parent[vertex] = root
--           tick("uf_compress")
--           return root
--
--       def union(self, a: Int, b: Int) -> Bool:
--           # CLRS UNION: find both roots, then apply union by rank (LINK).
--           # The Boolean result reports whether two components were joined.
--           left = self.find(a)
--           right = self.find(b)
--           tick("uf_union")
--           if left == right:
--               return False
--           # @link
--           if self.rank[left] < self.rank[right]:
--               self.parent[left] = right
--           elif self.rank[right] < self.rank[left]:
--               self.parent[right] = left
--           else:
--               # Equal ranks may choose either root; here the left root wins.
--               self.parent[right] = left
--               self.rank[left] = self.rank[left] + 1
--           return True
--   ```
--
--   ### `indexed_heap.algo`
--
--   ```python
--   # An indexed binary min-heap for Dijkstra's priority queue.
--   # vertices[position] and positions[vertex] are inverse on the active prefix.
--   # keys is indexed by vertex; position -1 means the vertex is not in the heap.
--   # Clients use nonnegative vertex identifiers, so pop_min can use -1 for empty.
--
--   class MinHeap:
--       vertices: Seq
--       positions: Seq
--       keys: Seq
--       size: Int
--
--       def __init__(self) -> None:
--           self.vertices = const(0)
--           self.positions = const(-1)
--           self.keys = const(0)
--           self.size = 0
--
--       def swap(self, i: Int, j: Int) -> None:
--           a = self.vertices[i]
--           b = self.vertices[j]
--           # @exchange
--           self.vertices[i] = b
--           self.vertices[j] = a
--           self.positions[a] = j
--           self.positions[b] = i
--           tick("heap_swaps")
--
--       def sift_up(self, i: Int) -> None:
--           # @up_loop
--           while i > 0:
--               parent = (i - 1) // 2
--               tick("heap_comparisons")
--               if self.keys[self.vertices[parent]] <= self.keys[self.vertices[i]]:
--                   return
--               self.swap(i, parent)
--               i = parent
--
--       def sift_down(self, i: Int) -> None:
--           # @down_loop
--           while 2 * i + 1 < self.size:
--               child = 2 * i + 1
--               right = child + 1
--               if right < self.size:
--                   tick("heap_comparisons")
--                   if self.keys[self.vertices[right]] < self.keys[self.vertices[child]]:
--                       child = right
--               # @compare_child
--               tick("heap_comparisons")
--               if self.keys[self.vertices[i]] <= self.keys[self.vertices[child]]:
--                   return
--               self.swap(i, child)
--               i = child
--
--       def push_or_decrease(self, vertex: Int, key: Int) -> None:
--           i = self.positions[vertex]
--           if i < 0:
--               self.keys[vertex] = key
--               i = self.size
--               self.vertices[i] = vertex
--               self.positions[vertex] = i
--               self.size += 1
--               self.sift_up(i)
--           else:
--               tick("heap_comparisons")
--               if key < self.keys[vertex]:
--                   self.keys[vertex] = key
--                   self.sift_up(i)
--
--       def pop_min(self) -> Int:
--           if self.size <= 0:
--               return -1
--           vertex = self.vertices[0]
--           last = self.size - 1
--           self.swap(0, last)
--           self.size = last
--           self.positions[vertex] = -1
--           if last > 0:
--               self.sift_down(0)
--           return vertex
--
--       def is_empty(self) -> Bool:
--           return self.size <= 0
--   ```
--
--   ### `sort_indices.algo`
--
--   ```python
--   # Order the identifiers [0, count) by their keys using a reusable binary heap.
--   # This supplies Kruskal's sort-by-weight step: insert every identifier, then
--   # extract minima. It is not the in-place HEAPSORT procedure from CLRS Chapter 6.
--   # Only identifiers are reordered; keys are unchanged. Equal-key identifiers
--   # may appear in either order.
--   from indexed_heap import MinHeap
--
--
--   def sort_indices(keys: Seq, count: Int) -> Seq:
--       queue = MinHeap()
--       result = const(0)
--       index = 0
--       # @insert
--       while index < count:
--           tick("sort_steps")
--           queue.push_or_decrease(index, keys[index])
--           index += 1
--       index = 0
--       # @extract
--       while index < count:
--           tick("sort_steps")
--           result[index] = queue.pop_min()
--           index += 1
--       return result
--   ```
--
--   ### `kruskal.algo`
--
--   ```python
--   # Minimum spanning forest by CLRS MST-KRUSKAL (fourth edition, Section 21.2).
--   # Edge identifiers are 0, ..., count - 1; endpoint arrays contain vertices
--   # in 0, ..., size - 1. The zero/one flag sequence represents the edge set A.
--   from union_find import UnionFind
--   from sort_indices import sort_indices
--
--
--   def kruskal(size: Int, sources: Seq, targets: Seq, weights: Seq, count: Int) -> Seq:
--       chosen = const(0)
--       # Construct one singleton set for each vertex (the textbook MAKE-SET loop).
--       sets = UnionFind(size)
--       order = sort_indices(weights, count)
--       index = 0
--       tick("kruskal")
--       # @scan
--       while index < count:
--           edge = order[index]
--           a = sources[edge]
--           b = targets[edge]
--           tick("kruskal")
--           left = sets.find(a)
--           right = sets.find(b)
--           # @test
--           if left != right:
--               # @select
--               chosen[edge] = 1
--               # @join
--               sets.union(a, b)
--           index += 1
--       return chosen
--   ```
--
--   <!-- algo2lean-supplemental-source -->
--   This supplemental handwritten analysis is separate from the released compiler source. Its additional analysis archive location is [here](https://github.com/lunjiah/algo2lean/releases/download/v0.1.4/algo2lean-clrs-analysis.zip), file `SubmissionAnalysis/Kruskal.lean` (SHA-256 `31533c2285238e53767bc6de90bc1566d00a73cc32c15629c14f0b68b081b640`). Publication and archive verification are tracked separately; the source is not raw compiler output.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/releases/download/v0.1.4/algo2lean-clrs-analysis.zip

import Definitions.Def_SubmissionAnalysis_Kruskal
import Theorems.Thm_KruskalAnalysis_call_contract

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem CLRS.Kruskal.correctness_and_running_time :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
        ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
          (sources targets weights : Algo2LeanGenerated.SeqRef),
          Algo.kruskal.kruskal.ValidInput heap
              (Prod.mk.{0, 0} size
                (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count)))) →
            KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
              Exists.{1} fun final =>
                Exists.{1} fun chosen =>
                  Exists.{1} fun selected =>
                    Algo.kruskal.kruskal.Call heap
                        (Prod.mk.{0, 0} size
                          (Prod.mk.{0, 0} sources
                            (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
                        final chosen ∧
                      Algo2Lean.Kruskal.MinimumSpanningForest
                          (KruskalInput.edges (heap.read sources) (heap.read targets)
                            (heap.read weights) count)
                          selected ∧
                        KruskalAnalysis.Flags (final.read chosen) selected ∧
                          heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                            LE.le.{0} heap.nextRef chosen ∧
                              LT.lt.{0} chosen final.nextRef ∧
                                heap.Increments final (heap.cost final) ∧
                                  LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                    (HMul.hMul.{0, 0, 0} C
                                      (CLRS.Kruskal.runtimeScale size.toNat count.toNat)) := by
  sorry
