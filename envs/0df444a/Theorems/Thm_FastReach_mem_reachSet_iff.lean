-- Prove2me | Theorems.Thm_FastReach_mem_reachSet_iff
-- name    : FastReach.mem_reachSet_iff
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T17:34:58.577238+00:00
-- url     : https://prove2.me/theorems/83e21e34-5146-4933-a57d-c2e5c671620a
-- title:
--   Neighbour closure computes the reachable set
-- statement:
--   Let $G$ be a simple graph on a finite vertex type $V$ with decidable adjacency, and recall the neighbour-closure operator
--
--   $$\operatorname{step}(s) \;=\; s \;\cup\; \{\, v \in V \;:\; \exists\, u \in s,\ u \sim_G v \,\},$$
--
--   together with $\operatorname{reachSet}(u) = \operatorname{step}^{\,|V|}(\{u\})$. This theorem asserts that the construction is correct: for all vertices $u, v$,
--
--   $$v \in \operatorname{reachSet}(u) \quad\Longleftrightarrow\quad v \text{ is reachable from } u \text{ in } G.$$
--
--   The forward direction is a straightforward induction on the number of rounds: $\{u\}$ consists of vertices reachable from $u$, and each round only adds vertices adjacent to something already known to be reachable, so reachability is preserved throughout.
--
--   The reverse direction needs the iteration count to be large enough. If $v$ is reachable from $u$ then some *path* joins them, and a path in a finite graph has length strictly less than $|V|$, since its vertices are distinct. An induction along that path shows that its endpoint lies in the $\ell$-th closure where $\ell$ is the path's length; because $\operatorname{step}$ is inflationary the closures are nested increasing, so the endpoint also lies in the $|V|$-th closure. Taking a path rather than an arbitrary walk is what makes the fixed iteration count $|V|$ sufficient.
--
--   The value of this statement is practical. It licenses replacing Mathlib's decision procedure for `SimpleGraph.Reachable` — which searches over all walks of length less than $|V|$ and is unusable past roughly ten vertices — by a `Finset` computation that evaluates directly. Any argument that needs to settle connectivity in a concrete finite graph, or to sum a quantity over configurations of a percolation weighted by whether two vertices are connected, can use it.
--
--   **Formalization Note** The statement is universally quantified over the vertex type, the graph, the adjacency-decidability instance and the two vertices, all implicit. Reachability is Mathlib's `SimpleGraph.Reachable`, i.e. `Nonempty (G.Walk u v)`, which is reflexive; correspondingly $u \in \operatorname{reachSet}(u)$ holds because the zeroth closure is $\{u\}$.
-- source:
--   Standard correctness statement for breadth-first / neighbour-closure reachability. Companion to the definition FastReachability; motivated by the infeasibility of Mathlib reachable_iff_exists_finsetWalkLength_nonempty (Mathlib/Combinatorics/SimpleGraph/Connectivity/Finite.lean) on graphs of more than ~10 vertices.

import Definitions.Def_FastReachability

namespace FastReach

/-- Neighbour closure iterated `|V|` times computes exactly the reachable set. -/
theorem mem_reachSet_iff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ reachSet G u ↔ G.Reachable u v := by sorry

end FastReach
