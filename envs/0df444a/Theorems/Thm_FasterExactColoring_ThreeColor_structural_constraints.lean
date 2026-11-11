-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_structural_constraints
-- name    : FasterExactColoring.ThreeColor.structural_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:02.766442+00:00
-- url     : https://prove2.me/theorems/a36431c9-06e6-4e35-994d-a150215347aa
-- title:
--   Lemma 4.4 — all six structural constraints
-- statement:
--   Let $G,F$ satisfy the source's preprocessing conditions and choose one internal root in each tree of $F$. Let $p,q,r,s,t,d$ be the computed counts of roots, other internal vertices, leaves, $S,T,D$, respectively. All six counts are nonnegative and
--   $$p+q+r+s+t=n,\quad d\le s,\quad4p+2q\le r,\quad s\le2r,\quad d\le8p,\quad t\le2s+d.$$
--   Here $n$ is the number of vertices of $G$. The six relations constitute Eq. (2) and constrain the final analysis; none is made an assumption of the main theorem.
--
--   Differences from the source:
--   - encoding: finite simple graphs and colors labeled 1 through k → SimpleGraph (Fin n) with decidable adjacency and Fin k colors labeled from zero; reason: finite relabeling represents every source instance, including the empty graph
--   - encoding: graph after the preprocessing of Section 4.2 → minimum degree three, acyclicity of ambient degree-three vertices, and a modified maximal bushy forest; valid internal roots and a maximal leaf matching where used; reason: these are exactly the source standing conditions, and counts are computed rather than assumed independent
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 4.4, p. 6 (PDF p. 8)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem structural_constraints (n : ℕ) (G : GraphInput n) (F : ForestData n)
  (roots : Finset (Fin n)) (h : forestPreprocessed G F) (hroot : F.rooted roots) :
  let a := counts G F roots ∅
  (0 ≤ a.p ∧ 0 ≤ a.q ∧ 0 ≤ a.r ∧ 0 ≤ a.s ∧ 0 ≤ a.t ∧ 0 ≤ a.d) ∧
  a.p+a.q+a.r+a.s+a.t = n ∧ a.d ≤ a.s ∧ 4*a.p+2*a.q ≤ a.r ∧
  a.s ≤ 2*a.r ∧ a.d ≤ 8*a.p ∧ a.t ≤ 2*a.s+a.d := by sorry

end FasterExactColoring.ThreeColor
