-- Prove2me | Theorems.Thm_FixedPolyominoSquare_SquareCounting_rectangular_dissection_bound
-- name    : FixedPolyominoSquare.SquareCounting.rectangular_dissection_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:27.180497+00:00
-- url     : https://prove2.me/theorems/fbf79fe9-2c5e-4041-8a23-ad398d5074c1
-- title:
--   Theorem 6.1 — rectangular-dissection bound
-- statement:
--   Let $D$ be an unordered partition of $\mathrm{Square}_n$ into at least two nonempty discrete rectangles, and let $I(D)$ be the number of adjacent-cell pairs belonging to different blocks. Join their unit seam segments whenever they share an endpoint. Then
--
--   $$I(D)\geq n,\qquad |C|\geq n\ \text{for every seam component }C.$$
--
--   For every fixed seam count $k\geq1$,
--
--   $$\bigl|\{D\in\mathrm{Part}_n:|D|\geq2,\ I(D)=k\}\bigr|\leq256^k.$$
--
--   All three conclusions are bundled. The count concerns unordered partitions and counts each seam only once, including all T-junction and crossing incidences.
--
--   Differences from the source:
--   - encoding: unordered rectangular dissections and connected components of the graph on common unit sides → finite sets of finite cell blocks, lexicographically oriented seam pairs and finite-path seam components; reason: finite enumeration introduces no block ordering or seam multiplicity; for n=0 or n=1 there is no qualifying nontrivial dissection
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 14, Theorem 6.1

import Definitions.Def_FixedPolyominoSquare_SquareCounting_RectangularPartitions

namespace FixedPolyominoSquare.SquareCounting

/-- Chen--Xie, Theorem 6.1, p. 14: all three assertions, including the
component-size bound and the absolute constant 256. -/
theorem rectangular_dissection_bound :
    (∀ (n : ℕ) (D : Finset Region), D ∈ Part n → 2 ≤ D.card →
      n ≤ I n D ∧ ∀ e ∈ seams n D, n ≤ (seamComponent n D e).card) ∧
    (∀ n k : ℕ, 1 ≤ k →
      ((Part n).filter fun D => 2 ≤ D.card ∧ I n D = k).card ≤ 256 ^ k) := by sorry

end FixedPolyominoSquare.SquareCounting
