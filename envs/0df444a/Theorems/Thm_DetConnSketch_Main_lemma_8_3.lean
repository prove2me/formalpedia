-- Prove2me | Theorems.Thm_DetConnSketch_Main_lemma_8_3
-- name    : DetConnSketch.Main.lemma_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:22.298042+00:00
-- url     : https://prove2.me/theorems/e0c50c98-d23c-4c0c-bc1d-532d3e447fe7
-- title:
--   Lemma 8.3 — a cut-space shift making $x\le y$ forces $L_x$ and $L_y$ to conflict in $P_{4k}$
-- statement:
--   Let $k \ge 0$, $m = k^2$, and let $x, y \in \mathbb F_2^m$ be distinct. If some $b$ in the binary cut space $B$ of $K_{k,k}$ satisfies
--   $$x + b \le y + b \quad\text{coordinatewise, the bits read as the integers } 0, 1,$$
--   then the two-lifts $L_x$ and $L_y$ are adjacent in the universal graph $P_{4k}$ on the $4k$ lifted vertices: $L_x \setminus L_y$ and $L_y \setminus L_x$ have different connected components.
--
--   It shows that the matrix of Eq. (4) is supported on edges of $P_{4k}$.
--
--   Differences from the source:
--   - encoding: x, y, b ∈ F_2^m with m = k²; P_{4k} → Fin k → Fin k → ZMod 2; universalGraph on LiftVertex k = (Fin k ⊕ Fin k) × ZMod 2 (4k vertices); reason: same objects with 0-based indices
--   - encoding: x + b ≤ y + b coordinatewise as integers in {0,1} → ((x + b) i j).val ≤ ((y + b) i j).val for all i, j; reason: ZMod.val is the integer 0 or 1
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 50 (PDF 54), Lemma 8.3

import Mathlib
import Definitions.Def_DetConnSketch_Main_UniversalGraph
import Definitions.Def_DetConnSketch_Main_TwoLift

namespace DetConnSketch.Main

/-- Lemma 8.3: if `x, y ∈ F_2^m` are distinct and some `b` in the cut space `B` has
`x + b ≤ y + b` coordinatewise (the bits read as the integers `0, 1`), then the two-lifts `L_x`
and `L_y` are adjacent in the universal graph `P_{4k}` on the `4k` lifted vertices. -/
theorem lemma_8_3 (k : ℕ) (x y b : EdgeLabel k) (hxy : x ≠ y) (hb : b ∈ cutSpace k)
    (hle : ∀ i j, ((x + b) i j).val ≤ ((y + b) i j).val) :
    (universalGraph (LiftVertex k)).Adj (lift x) (lift y) := by sorry

end DetConnSketch.Main
