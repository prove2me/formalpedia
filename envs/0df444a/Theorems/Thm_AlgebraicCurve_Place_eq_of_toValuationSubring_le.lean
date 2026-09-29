-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_eq_of_toValuationSubring_le
-- name    : AlgebraicCurve.Place.eq_of_toValuationSubring_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/fb69d928-4332-50e8-b7c2-94f8dff26d89
-- title:
--   Places are determined by containment of their valuation rings
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ and $w$ be places of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): each consists of a valuation subring `toValuationSubring` of $F$ which contains $\mathrm{image}$ of $K$ under the structural map (i.e. $\mathrm{algebraMap}_{K,F}(a)$ lies in it for every $a \in K$), which is not the whole of $F$, and which is a principal ideal ring — so, being a proper valuation subring with principal ideals, a discrete valuation ring. Assume that the valuation subring of $v$ is contained in that of $w$. The conclusion is that $v = w$ as places, equality of the structures being equality of the underlying valuation subrings. Thus the valuation subrings of such places are pairwise incomparable under inclusion, and in particular each is a maximal proper subring of $F$ among them.
--
--   This is the standard fact that distinct places of a function field have incomparable valuation rings, equivalently that the valuation ring of a place is maximal among proper subrings of this kind; it is the rigidity statement that lets one recognise a place from a one-sided containment. It is used in the Čerednik–Drinfeld part of the development, in the identification of pullbacks and restrictions of places along field extensions and of the action of semilinear automorphisms on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_eq_of_toValuationSubring_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.eq_of_toValuationSubring_le
    {K F : Type*} [Field K] [Field F] [Algebra K F] {v w : AlgebraicCurve.Place K F}
    (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w := by sorry
