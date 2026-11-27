-- Prove2me | Theorems.Thm_EdmondsPolytope_edmonds_perfect_matching_polytope
-- name    : EdmondsPolytope.edmonds_perfect_matching_polytope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:39:30.801802+00:00
-- url     : https://prove2.me/theorems/9b213aae-7f38-50e2-8c18-0eb241f17e94
-- title:
--   Edmonds Polytope: edmonds perfect matching polytope
-- statement:
--   **Edmonds' perfect matching polytope theorem** (Edmonds 1965): the convex hull of the
--   incidence vectors of the perfect matchings of a finite simple graph is described by
--   nonnegativity, the degree equations and the odd-set inequalities.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/Solution.lean#L64-L67
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/Solution.lean#L64-L67

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Definitions.Def_EdmondsPolytope_Solution
public import Theorems.Thm_MatchingPolytope_edmonds_perfect_matching_polytope

set_option autoImplicit true
@[expose] public section
public section
open EdmondsPolytope

theorem EdmondsPolytope.edmonds_perfect_matching_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (perfectMatchingVectors G) = edmondsPolytope G := by sorry
