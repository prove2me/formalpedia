-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one
-- name    : AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/4dbc74e7-b134-531f-abe4-aa5351dad958
-- title:
--   Laurent expansion at a place of degree one
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $w$ be a place of $F$ over $K$: that is, a valuation subring of $F$ which contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. Let $w$ have degree one, the degree being the $K$-dimension of the residue field of the local ring $w$, and let $t \in F$ satisfy $\operatorname{ord}_w t = 1$, where $\operatorname{ord}_w$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $w$ (so $\operatorname{ord}_w$ takes the value $0$ at $0$ by the convention $\log 0 = 0$). The assertion is that there exists a $K$-algebra homomorphism $\varphi$ from $F$ to the field $K(\!(T)\!)$ of formal Laurent series over $K$, realised as Hahn series over $\mathbb{Z}$, such that $\varphi(t)$ is the monomial $T =$ `HahnSeries.single 1 1`, and such that for every $x \in F$ the order of the Laurent series $\varphi(x)$ equals $\operatorname{ord}_w x$; the latter identity is stated for all $x$ without exception, both sides being $0$ at $x = 0$. In particular $\varphi$ is injective. No uniqueness is claimed, and no finiteness hypothesis on $F$ over $K$ is imposed.
--
--   This is the classical expansion of elements of a function field as Laurent series in a local parameter at a place of degree one (a rational point), stated for $F$ itself rather than for its completion. It is used to produce local parameters with prescribed analytic order, and in the count of fixed points of iterates of a Frobenius place on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1)
    (t : F) (ht : w.ord t = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ t = HahnSeries.single (1 : ℤ) (1 : K) ∧ ∀ x : F, (φ x).order = w.ord x := by sorry
