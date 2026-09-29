-- Prove2me | Theorems.Thm_ComponentSegmentInOpenBall
-- name    : ComponentSegmentInOpenBall
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T00:18:13.862673+00:00
-- url     : https://prove2.me/theorems/8eb9fdd2-ebea-40d1-80e5-c102063bd3cd
-- title:
--   A complement component absorbs a segment in an open ball
-- statement:
--   Let $U$ be an open region and let $C$ be a connected component of its complement, in the maximality sense encoded by `ComplementComponent Uᶜ C`. If $y\in C$, $z$ lies in the open metric ball $B(y,r)$, and the entire ball is contained in $U$, then the whole segment from $y$ to $z$ remains in $C$.
--
--   In other words, a complement component cannot be left by a straight segment that stays inside a ball disjoint from the complement of $U$. This local absorption principle is the step used to extend polygonal paths while remaining in the same complement component.
--
--   **Formalization Note** The hypothesis `z ∈ Metric.ball y r` forces the radius to be positive, so convexity of the metric ball places the segment in the ball; maximality of the component then absorbs the connected union of $C$ and that segment.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/ComponentSegmentInOpenBall.lean#L1-L38

import Definitions.Def_ComplementComponent

open Classical
noncomputable section

theorem ComponentSegmentInOpenBall
    (U C : Set (EuclideanSpace ℝ (Fin 2)))
    (y z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ComplementComponent Uᶜ C →
      y ∈ C →
        z ∈ Metric.ball y r →
          Metric.ball y r ⊆ U →
            segment ℝ y z ⊆ C := by sorry
