-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_2_3_one_disk
-- name    : DelaunayStretch.lemma_2_3_one_disk
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:18.306217+00:00
-- url     : https://prove2.me/theorems/ba7dc14b-64e8-4a07-b0c2-203e91a9f2a5
-- title:
--   Lemma 2.3 — one disk: $r\eta\le\frac\pi2\|u-v\|$, one-disk chains, and the chain inequality needs $U\ge\pi/2$
-- statement:
--   Let $u\ne v$ be two points on a circle of radius $r$, and let $\eta\in(0,\pi]$ be the smaller central angle between them. Then
--
--   $$
--   r\eta\le\frac\pi2\,\|u-v\|,
--   $$
--
--   with equality if and only if $\eta=\pi$. Consequently:
--
--   1. every disk chain with $n=1$ satisfies $P(u,v)\le\frac\pi2\|u-v\|$, with equality if and only if the center of $O_1$ lies on the $x$-axis;
--   2. the chain inequality can hold only at levels $U\ge\pi/2$;
--   3. at every level $U\ge\pi/2$ it holds for all disk chains with one disk.
--
--   This is the base case of the potential criterion and explains the lower limit $\pi/2$ for every level.
--
--   **Formalization Note** The smaller central angle is the unoriented angle $\angle uov\in[0,\pi]$ at the center $o$; it is positive because $u\ne v$.
--
--   Differences from the source:
--   - encoding: the smaller central angle η ∈ (0, π] between u and v → the unoriented angle ∠ u o v at the center o (EuclideanGeometry.angle); reason: the unoriented angle is the smaller central angle; it lies in (0, π] for u ≠ v on the circle
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: P(u, v), the length of a shortest path from u to v in the ladder graph → the infimum of the weights of walks from u to v in the ladder graph (vertex labels, not points); reason: the ladder graph is finite with nonnegative weights (rails by (C4) and (2.1)), so the infimum is attained and is the shortest-path length
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 2.3, p.13

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality

namespace DelaunayStretch

/-- **Lemma 2.3 (One disk)** (p.13). Let `u ≠ v` be two points on a circle of radius `r`, and
let `η ∈ (0, π]` be the smaller central angle between them. Then `rη ≤ (π/2)‖u − v‖`, with
equality if and only if `η = π`. Consequently, every disk chain with `n = 1` satisfies
`P(u, v) ≤ (π/2)‖u − v‖`, with equality if and only if the center of `O₁` lies on the
`x`-axis. In particular, the chain inequality can hold only at levels `U ≥ π/2`, and at every
such level it holds for all disk chains with one disk.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 2.3, p.13.

**Formalization Note** The circle has center `o`; the smaller central angle is the unoriented
angle `∠ u o v ∈ [0, π]` (`EuclideanGeometry.angle`), which is positive since `u ≠ v`. -/
theorem lemma_2_3_one_disk :
    (∀ (o u v : ℂ) (r : ℝ), u ∈ Metric.sphere o r → v ∈ Metric.sphere o r → u ≠ v →
      r * EuclideanGeometry.angle u o v ≤ Real.pi / 2 * dist u v ∧
        (r * EuclideanGeometry.angle u o v = Real.pi / 2 * dist u v ↔
          EuclideanGeometry.angle u o v = Real.pi)) ∧
    (∀ C : DiskChain, C.IsDiskChain → C.n = 1 →
      C.shortestPath ≤ Real.pi / 2 * dist C.u C.v ∧
        (C.shortestPath = Real.pi / 2 * dist C.u C.v ↔ (C.O 1).center.im = 0)) ∧
    (∀ U : ℝ, ChainInequality U → Real.pi / 2 ≤ U) ∧
    (∀ U : ℝ, Real.pi / 2 ≤ U → ∀ C : DiskChain, C.IsDiskChain → C.n = 1 →
      C.shortestPath ≤ U * dist C.u C.v) := by sorry

end DelaunayStretch
