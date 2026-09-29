-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
-- name    : AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/4931a8fd-65e8-5b16-a93e-5c3a0bb8f3e0
-- title:
--   Fundamental inequality sum_w e_w f_w ≤ [F':F]
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields with compatible $K$-algebra structures forming a scalar tower, with $F'$ finite-dimensional over $F$ and $F'/F$ separable. Here a place of a field $L$ over $K$ is a valuation subring of $L$ that contains the image of $K$ under the structure map, is not all of $L$, and is a principal ideal ring; its residue field is the residue field of that local ring. Let $v$ be such a place of $F$ over $K$, and let $S$ be a finite set of places of $F'$ over $K$ such that every $w \in S$ restricts to $v$, the restriction of $w$ to $F$ being the place whose valuation subring is the preimage of that of $w$ under $\mathrm{algebraMap}\ F\ F'$. For $w \in S$, the ramification index $e(w \mid F)$ is the least $n > 0$ for which some nonzero $f \in F$ has $\mathrm{ord}_w(\mathrm{algebraMap}\ F\ F'\,f) = n$, and the inertia degree $f(w \mid F)$ is the degree of the residue field of $w$ over the residue field of its restriction to $F$. The conclusion is the inequality of integers $\sum_{w \in S} e(w \mid F)\, f(w \mid F) \le [F' : F]$.
--
--   This is the fundamental inequality for places of a finite separable extension of function fields: any finite collection of places of $F'$ lying over a fixed place $v$ of $F$ contributes at most $[F':F]$ to the sum of the products of ramification index and inertia degree, with no requirement that the collection exhaust the fibre over $v$. It is used to show that a place over $v$ is unique once a partial sum already attains $[F':F]$, and in this form feeds the counting of cusps and of poles of modular functions on $X_0(\ell)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) (S : Finset (Place K F'))
    (hS : ∀ w ∈ S, w.restrict F = v) :
    ∑ w ∈ S, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) ≤ (Module.finrank F F' : ℤ) := by sorry
