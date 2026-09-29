-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
-- name    : AlgebraicCurve.Place.taylorCoeff_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/0a64baff-d3e6-540a-9d38-bf5652780b80
-- title:
--   Additivity of Taylor coefficients at a rational place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F/K$ in the project's sense: a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, i.e. the map from $K$ to the residue field $\mathcal O_v/\mathfrak m_v$ is surjective, and let $t \in F$ satisfy `v.ord t = 1` for the project's order function, expressing that $t$ is a uniformiser at $v$. Let $f, g \in \mathcal O_v$ and let $r \in \mathbb N$. Then the $r$-th Taylor coefficient along $t$ is additive: `taylorCoeff v t r (f + g) = taylorCoeff v t r f + taylorCoeff v t r g` in $K$. Here `taylorCoeff v t r f` is the element of $K$ obtained by applying `v.evalAt` (the inverse image in $K$ of the residue class of an element of $\mathcal O_v$, and $0$ off $\mathcal O_v$) to the $r$-th remainder `taylorRem v t f r`, defined by `taylorRem v t f 0 = f` and `taylorRem v t f (r+1) = (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹`.
--
--   This is one half of the $K$-linearity of the jet map $f \mapsto (a_0(f), a_1(f), \dots)$ sending a function regular at a rational place $v$ to its Taylor coefficients along a uniformiser; together with the homogeneity statement it makes each Taylor coefficient a $K$-linear functional on $\mathcal O_v$. It is used throughout the development of Taylor expansions at places, for instance in the identification of the coefficients of polynomial expressions and in the analysis of jet determinants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorCoeff_add.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorCoeff_add
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (r : ℕ) :
    taylorCoeff v t r (f + g) = taylorCoeff v t r f + taylorCoeff v t r g := by sorry
