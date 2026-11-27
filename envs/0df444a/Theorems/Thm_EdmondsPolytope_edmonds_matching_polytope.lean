-- Prove2me | Theorems.Thm_EdmondsPolytope_edmonds_matching_polytope
-- name    : EdmondsPolytope.edmonds_matching_polytope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:39:34.400001+00:00
-- url     : https://prove2.me/theorems/80fce51d-1902-461f-9aca-a298dab2f95f
-- title:
--   Edmonds Polytope: edmonds matching polytope
-- statement:
--   **Edmonds' matching polytope theorem**: the convex hull of the incidence vectors of the
--   matchings of a finite simple graph is described by nonnegativity, the degree inequalities and
--   the odd-set inequalities.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/Solution.lean#L72-L75
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/Solution.lean#L72-L75

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Definitions.Def_EdmondsPolytope_Solution
public import Theorems.Thm_MatchingPolytope_edmonds_matching_polytope

set_option autoImplicit true
@[expose] public section
public section
open EdmondsPolytope

theorem EdmondsPolytope.edmonds_matching_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (matchingVectors G) = matchingPolytope G := by sorry
