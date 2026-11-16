-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_maximal_star_consequences
-- name    : FasterExactColoring.ThreeColor.Supplement.maximal_star_consequences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:51:56.326863+00:00
-- url     : https://prove2.me/theorems/8b814153-83d8-483b-9b39-534a27016538
-- title:
--   Lemma 5.1 (used in the proof of Theorem 1.3) — maximal-star degree consequences
-- statement:
--   Let $P=(G,I,S)$ be any valid terminal restricted four-coloring instance, with $U=V(G)\setminus(I\cup S)$. Supply the two inclusion-maximal vertex-disjoint $K_{1,3}$ packings of Section 5.2, and use $S_{\star1},U_{\star2},S'$ as defined there. Both conclusions hold:
--   $$\Delta(G[S\setminus S_{\star1}])\le2,\qquad
--    |N_G(u)\cap S'|\le2\quad\text{for every }u\in U\setminus U_{\star2}.$$
--   The first conclusion is pointwise at each vertex, so it also covers the empty induced graph. Stars are subgraphs and need not be induced. These are the degree restrictions required by the terminal decomposition algorithms.
--
--   Differences from the source:
--   - encoding: terminal instances after the two maximal-star preprocessing steps → valid restricted instances with supplied valid inclusion-maximal star packings, all structural counts computed from them; reason: the explicit finite input includes the graph, restrictions and packings; its size is polynomial in the original vertex count
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.1, p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_StarPackings

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem maximal_star_consequences {n : ℕ} (P : Restricted n) (K : StarPackings n)
    (hP : P.valid) (ht : P.terminal) (hK : K.valid P) :
  (∀ v ∈ P.S \ K.firstVertices, degreeIn P.G (P.S \ K.firstVertices) v ≤ 2) ∧
  (∀ u ∈ P.U \ K.secondCenters, degreeIn P.G (K.remainingS P) u ≤ 2) := by sorry

end FasterExactColoring.ThreeColor.Supplement
