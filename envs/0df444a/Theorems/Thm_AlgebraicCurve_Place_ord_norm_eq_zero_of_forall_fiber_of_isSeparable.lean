-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber_of_isSeparable
-- name    : AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/80e0104d-cc26-5191-a4f5-7b5f6fa64a66
-- title:
--   Norm has trivial order at v when f does on the fibre
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields with $F$ and $F'$ $K$-algebras, $F'$ an $F$-algebra, the three structures forming a scalar tower, and with $F'/F$ finite and separable; assume $F'$ satisfies `HasPrincipalDivisors K F'`, i.e. every nonzero $g \in F'$ admits a finitely supported function $D$ on the places of $F'$ over $K$ with $D(w) = \operatorname{ord}_w(g)$ for every such place $w$ and with $\deg D = \sum_w D(w)\,\deg w = 0$. Here a place of $F$ over $K$ is a valuation subring of $F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring, and $\operatorname{ord}_v$ is the associated normalised order function, namely minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation. Let $f \in F'$ be nonzero and let $v$ be a place of $F$ over $K$. Assume that $\operatorname{ord}_w(f) = 0$ for every $w$ in the fibre `v.fiber F'`, the finite set of places of $F'$ over $K$ restricting to $v$. Then $\operatorname{ord}_v\bigl(N_{F'/F}(f)\bigr) = 0$, where $N_{F'/F}$ is `Algebra.norm F`.
--
--   This is the standard fact that the norm of a function with neither zero nor pole at any place above $v$ has order $0$ at $v$, in the form needed for the separable case. It is used in the proof of Weil reciprocity for functions pulled back along $F \to F'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber_of_isSeparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (v : Place K F) (h : ∀ w ∈ v.fiber F', w.ord f = 0) : v.ord (Algebra.norm F f) = 0 := by sorry
