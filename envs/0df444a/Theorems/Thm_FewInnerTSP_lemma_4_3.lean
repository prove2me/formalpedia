-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_4_3
-- name    : FewInnerTSP.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:32:36.960411+00:00
-- url     : https://prove2.me/theorems/a88bdedb-ae4e-4967-95fe-8515350ad3f0
-- title:
--   Lemma 4.3 (Uniform local convex-boundary occupancy)
-- statement:
--   Fix a closed axis-aligned observation square $D$ (center $c$, side $R>0$). There is a constant $C>0$, depending only on $D$, such that for every finite planar set $W$ and every dyadic scale $s=2^{-j}$, $j\ge0$, the boundary of the convex hull of $W$ meets at most
--   $$C/s=C\cdot2^{j}$$
--   half-open cells of the side-$s$ grid inside $D$. The constant does not depend on the number, spacing or coordinate spread of the vertices.
--
--   This is why a convex boundary is one-dimensional at every scale: $O(s^{-1})$ occupied cells instead of the $O(s^{-2})$ of a planar set, which Lemma 4.4 turns into a polylogarithmic charge.
--
--   **Formalization Note** "Meets at most $C/s$ cells" is stated as a finite set of cell indices of size at most $C2^j$ containing every cell that meets the clipped boundary.
--
--   Differences from the source:
--   - generalization: within a fixed bounded observation square → for every closed axis-aligned square D, with the constant depending on D only; reason: specializes to the page's fixed box, e.g. [−5,5]² of Remark B.2
--   - generalization: a convex polygonal boundary → the frontier of the convex hull of any finite set W, degenerate hulls (a segment, a point) included; reason: every convex polygon is such a hull, and the skeleton with |H₀| = 2 is a segment
--   - encoding: O(s⁻¹) cells of a side-s grid → a finite index set of size ≤ C·2^j containing every half-open cell meeting the clipped boundary, s = 2^{−j}, j ≥ 0; reason: scales s ≤ 1 as in §4.2
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.3, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_FewInnerTSP_Charges

namespace FewInnerTSP

/-- **Lemma 4.3 (Uniform local convex-boundary occupancy).** Li, Ma, Gong, *Exact Euclidean TSP with Few
Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.3,
p.7 (PDF p.9): "Within a fixed bounded observation square, a convex polygonal boundary intersects O(s−1)
cells of a side-s grid. The constant is independent of the number, spacing, and global coordinate spread
of its vertices."

For every closed axis-aligned observation square `D` (center `c`, side `R > 0`) there is `C > 0` such
that for every finite planar set `W` and every dyadic scale `s = 2^{-j}`, `j ≥ 0`, at most `C/s = C·2^j`
half-open cells of the side-`s` grid meet `∂ CH(W) ∩ D`.

**Formalization Note** The boundary is `frontier (convexHull ℝ W)`, which for a nondegenerate polygon is
its boundary polygon, and for collinear `W` the hull segment itself. The bound is stated by a finite set of
cell indices containing every cell that meets the clipped boundary. Scales are `s ≤ 1` (§4.2's `j ≥ 0`). -/
theorem lemma_4_3 (c : Pt) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset Pt) (j : ℕ), ∃ G : Finset (ℤ × ℤ),
      (∀ g : ℤ × ℤ, (gridCell j g.1 g.2 ∩ frontier (convexHull ℝ (W : Set Pt)) ∩
          closedSquare c R).Nonempty → g ∈ G) ∧
      (G.card : ℝ) ≤ C * 2 ^ j := by sorry

end FewInnerTSP
