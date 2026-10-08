-- Prove2me | Theorems.Thm_ChinesePostman_Matching_parity_of_edge_disjoint_paths
-- name    : ChinesePostman.Matching.parity_of_edge_disjoint_paths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:46.418979+00:00
-- url     : https://prove2.me/theorems/98e145cd-1cfa-48fd-90b6-21a0cb31bf55
-- title:
--   §3, pp. 92–93 — the disjoint matching paths satisfy parity
-- statement:
--   Let $M$ pair all odd-degree nodes of a finite loopless multigraph, and choose edge-simple paths for its pairs that share no edge across distinct pairs. Define $x_e=1$ when edge $e$ lies on one of these paths and $x_e=0$ otherwise. Then there are nonnegative integers $w_v$ such that
--
--   $$
--   \sum_{e\ni v}x_e=2w_v+\mathbf1_{v\text{ odd}}\qquad(v\in N).
--   $$
--
--   Thus the union of the matching paths is a feasible parity correction.
--
--   **Formalization Note** Reversed orientations of the same matching path count as one path; the indicator uses their union. No lengths or connectivity are needed for this parity claim.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 92–93, §3, paragraph following uncrossing, https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, pp. 92–93: the union of disjoint matching paths satisfies the parity equations. -/
theorem parity_of_edge_disjoint_paths
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (f : V → V) (hf : IsOddPerfectMatching G f)
    (P : V → List V × List E) (hP : MatchingPaths G f P) :
    IsParitySolution G (pathIndicator G P) := by sorry
end ChinesePostman.Matching
