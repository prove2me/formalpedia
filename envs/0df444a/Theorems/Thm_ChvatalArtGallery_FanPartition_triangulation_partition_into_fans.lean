-- Prove2me | Theorems.Thm_ChvatalArtGallery_FanPartition_triangulation_partition_into_fans
-- name    : ChvatalArtGallery.FanPartition.triangulation_partition_into_fans
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:14:39.149978+00:00
-- url     : https://prove2.me/theorems/2f38f448-abfe-472e-990e-56fe5d616601
-- title:
--   Theorem (Chvátal 1975, p. 39) — every n-triangulation can be partitioned into at most ⌊n/3⌋ fans
-- statement:
--   Let $n \ge 3$ and let $G$ be an $n$-triangulation: a triangulated $n$-gon, given by its vertices $0,\dots,n-1$ in cyclic order and a maximal set $D$ of pairwise non-crossing diagonals. Then the triangles of $G$ can be partitioned into $m$ fans with
--   $$m \le \left\lfloor \frac{n}{3} \right\rfloor .$$
--   Here a fan is a nonempty, dual-connected set of triangles of $G$ (a sub-polygon of $G$) having a vertex that meets all of its inner edges, and a partition into fans is a family of fans, pairwise disjoint as sets of triangles, covering every triangle of $G$.
--
--   This is Chvátal's combinatorial theorem. Since each fan of a triangulated polygon is visible from its centre, it yields the art gallery theorem: every simple polygon with $n$ walls can be guarded by $\lfloor n/3\rfloor$ guards.
--
--   **Formalization Note.** The planar graph of the paper is encoded as the labelled $n$-cycle plus a maximal set of non-crossing diagonals (the standard equivalent description of a triangulated polygon, since Mathlib has no planar embeddings). "Partitioned into $m$ fans" is made explicit as a finset $P$ of fans that are pairwise disjoint as sets of triangles and cover all triangles; fans may share vertices and edges. Fans are required to be dual-connected and to have a centre on all their inner edges; dropping either clause would trivialize or weaken the theorem. $[n/3]$ is the floor, `n / 3` in ℕ. The only size hypothesis is $n \ge 3$. The geometric corollary (Klee's art gallery bound) is not part of this statement.
-- source:
--   Chvátal, A combinatorial theorem in plane geometry, J. Combin. Theory Ser. B 18 (1975), p. 39, Theorem ("Every n-triangulation can be partitioned into m fans where m ≤ [n/3].")

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation

namespace ChvatalArtGallery.FanPartition

/-- Theorem (Chvátal 1975, p. 39): every n-triangulation can be partitioned into m fans where
m ≤ ⌊n/3⌋. -/
theorem triangulation_partition_into_fans (n : ℕ) (hn : 3 ≤ n) (D : Finset (Sym2 (Fin n)))
    (hD : IsTriangulation n D) :
    ∃ P : Finset (Finset (Finset (Fin n))), IsFanPartition n D P ∧ P.card ≤ n / 3 := by sorry

end ChvatalArtGallery.FanPartition
