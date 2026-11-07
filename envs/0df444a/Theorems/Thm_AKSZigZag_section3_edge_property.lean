-- Prove2me | Theorems.Thm_AKSZigZag_section3_edge_property
-- name    : AKSZigZag.section3_edge_property
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:13.091215+00:00
-- url     : https://prove2.me/theorems/d2be9af3-190f-4124-a31e-74db14e45aa1
-- title:
--   §3, p.5 — edge property: after a bipartite network, every edge is ordered
-- statement:
--   Split the $m$ registers into $A=\{1,\dots,\lfloor m/2\rfloor\}$ and $B=\{\lfloor m/2\rfloor+1,\dots,m\}$. Let $N$ be a comparator network every switch of which joins a register $R_1\in A$ to a register $R_2\in B$ and puts the smaller element into $R_1$. Run $N$ on distinct contents.
--
--   Then at the end, for every switch $(R_1,R_2)$ of $N$,
--   $$
--   \text{content}(R_1)<\text{content}(R_2).
--   $$
--
--   This is the key observation behind the §3 halver: an edge, once compared, stays ordered, because the content of $R_1$ only decreases and that of $R_2$ only increases.
--
--   Differences from the source:
--   - generalization: a network defined by a bipartite graph between A and B, contents a permutation of 1,...,m → any network whose switches all go from A to B, in any order and possibly repeated, contents distinct elements of any linear order; reason: the network of a bipartite graph is such a network, and permutations of 1..m are distinct contents
--   - encoding: registers 1,...,m with A = (1,...,⌊m/2⌋) → Fin m, A = {i | i < m/2}; reason: 0-based indexing; same instances
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §3, p.5 ("Note first that a comparator network defined by any bipartite graph …")

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

namespace AKSZigZag

open AKSSorting.Core

/-- **The edge property** (AKS, STOC 1983, doi:10.1145/800061.808726, §3, p.5): "a comparator
network defined by any bipartite graph has the property that if R1 ∈ A and R2 ∈ B are connected
by an edge then the content of R1 is less than that of R2."

Let `N` be a comparator network on `m` registers each of whose comparators `(i, j)` joins a
register `i` of `A = (1, …, ⌊m/2⌋)` to a register `j` of `B = (⌊m/2⌋+1, …, m)` (smaller element
to `A`). Then for every input with distinct contents, at the end, the content of `i` is less than
the content of `j` for every comparator `(i, j)` of `N`.

**Formalization Note.** 0-based registers: `A` is `{i | i < ⌊m/2⌋}`. The edges of the graph are
the comparators of `N`, in any order and possibly repeated. Contents come from any linear order
and are distinct (the paper's permutations of `1, …, m`). -/
theorem section3_edge_property {m : ℕ} (N : ComparatorNetwork m)
    (hN : ∀ L ∈ N.layers, ∀ p ∈ L, p.1.val < m / 2 ∧ m / 2 ≤ p.2.val)
    {β : Type} [LinearOrder β] (x : Fin m → β) (hx : Function.Injective x) :
    ∀ L ∈ N.layers, ∀ p ∈ L, N.eval x p.1 < N.eval x p.2 := by sorry

end AKSZigZag
