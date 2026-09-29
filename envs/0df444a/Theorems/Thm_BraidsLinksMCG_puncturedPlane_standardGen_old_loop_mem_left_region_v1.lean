-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_standardGen_old_loop_mem_left_region_v1
-- name    : BraidsLinksMCG.puncturedPlane_standardGen_old_loop_mem_left_region_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T22:49:55.104244+00:00
-- url     : https://prove2.me/theorems/5d1ed36a-e1b8-40a1-b1c7-d2aa6acf6004
-- title:
--   The old standard loops stay inside the left piece of the matched cover
-- statement:
--   This is the pointwise containment that the left factor of the matched two-piece cover needs. The left piece is the set of points of the plane punctured at 1, ..., n+1 whose real part is less than n+1, or whose imaginary part is positive, or which lie within distance 1/2 of the point n+2. For each old index j with j < n, the standard loop of the n+1-puncture plane at the lifted index j.castSucc runs from the base point n+2 out along a parabola to the half-integer (j+1) + 1/2, once counterclockwise around the circle of radius 1/2 about the puncture j+1, and back. Every point of the circular leg has real part at most n + 1/2, which is strictly less than n+1, so the first disjunct holds throughout. On the approach leg the imaginary part is t(1-t), which is strictly positive for t strictly between 0 and 1, so the second disjunct holds in the interior; at t = 0 the point is the base point n+2, whose distance to n+2 is zero, so the third disjunct holds; and at t = 1 the point is the half-integer (j+1) + 1/2, whose real part is at most n + 1/2, so the first disjunct holds. This supplies the coordinate containment needed for a later pointed equivalence between the left factor and the fundamental group of the plane punctured at 1, ..., n; it does not assert that containment alone proves that equivalence. It is the left-loop counterpart of the Proved theorem puncturedPlane_standardGen_new_loop_mem_right_factor_v1.
-- source:
--   The definition file Def_BraidsLinksMCG_StandardLoops.lean gives standardLoop (n+1) j.castSucc = approachPath . circlePath . approachPath.symm, with approachFun (n+1) j t of imaginary part t(1-t) and real part (1-t)(n+1) + t((j:N)+3/2), and circleFun (n+1) j t of real part (j:N)+1+(1/2)cos(2*pi*t). Since j < n, the maximal real part on the circle is (n-1)+1+1/2 = n+1/2 < n+1, so the whole circle satisfies the first disjunct. On the approach leg the imaginary part t(1-t) is positive in the interior, so the second disjunct covers the interior and the third covers the single remaining endpoint t = 0, where the point is the base point n+2 itself.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

namespace BraidsLinksMCG

theorem puncturedPlane_standardGen_old_loop_mem_left_region_v1 (n : ℕ) (j : Fin n) (t : unitInterval) :
    (standardLoop (n + 1) j.castSucc t).1.re < ((n : ℕ) + 1 : ℝ) ∨
      0 < (standardLoop (n + 1) j.castSucc t).1.im ∨
      dist (standardLoop (n + 1) j.castSucc t).1 (((n : ℕ) + 2 : ℕ) : ℂ) < (1 / 2 : ℝ) := by sorry

end BraidsLinksMCG
