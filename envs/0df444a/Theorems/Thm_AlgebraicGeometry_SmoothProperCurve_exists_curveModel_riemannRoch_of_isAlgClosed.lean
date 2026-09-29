-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/09e588e1-1e93-5e17-b497-6997ff2c9d6f
-- title:
--   Riemann–Roch for geometric fibres of smooth proper curves
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a morphism which is proper, smooth of relative dimension $1$ and geometrically integral, let $k$ be an algebraically closed field and let $s : \operatorname{Spec} k \to \operatorname{Spec} R$ be a morphism (a $k$-point of the base). The assertion is the existence of: a field $L$ with a $k$-algebra structure; a `CurveModel k L`, that is a scheme $M.C$ with an integral structure and a proper, smooth of relative dimension $1$ morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} k$, together with a ring isomorphism from $L$ onto the function field of $M.C$ compatible with the map $k \to M.C$-function field induced by $M.\mathrm{toBase}$, a bijection from the closed points of $M.C$ onto the places of $L/k$ (valuation subrings of $L$ containing the image of $k$, proper, and principal ideal rings) matching the image of each local ring in $L$ with the corresponding valuation subring, and the property that every finite set of points of $M.C$ lies in an affine open; an isomorphism of schemes $e : M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ with $e$ followed by the second projection equal to $M.\mathrm{toBase}$; and a divisor $K_c$ of $L/k$ (a finitely supported $\mathbb{Z}$-valued function on places) and a natural number $g$ such that for every divisor $D$ of $L/k$, $$\ell(D) - \ell(K_c - D) = \deg D + 1 - g,$$ where $\ell(D)$ is the $k$-dimension of the Riemann–Roch space of $D$ inside $L$ and $\deg$ is the additive extension of the degree function on places.
--
--   This is the Riemann–Roch theorem on the geometric fibre $C \times_R \operatorname{Spec} k$ of a smooth proper relative curve, packaged as the existence of a function-field model of that fibre carrying a canonical divisor and a genus. It is used in the relative Picard constructions, where hypotheses of the shape "for every model of a geometric fibre and every Riemann–Roch datum $(K_c,g)$ …" must be known to be non-vacuous.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g : ℕ),
      ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by sorry
