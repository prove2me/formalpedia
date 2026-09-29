-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/a0bf4784-2e16-5f3b-a6ea-faaf67fe6de2
-- title:
--   Geometric fibres of smooth proper curves are curve models
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme and let $c \colon C \to \operatorname{Spec} R$ be a morphism which is proper, smooth of relative dimension $1$ and geometrically integral, and let $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ be any morphism with $k$ an algebraically closed field. The assertion is that there exist a type $L$ carrying a field structure and a $k$-algebra structure such that: $L$ is a curve over $k$ in the sense of the project's predicate `IsCurveOver`, i.e. every nonzero $f \in L$ has a divisor of degree $0$ recording its orders at all places of $L/k$, the residue field of every place is a finite $k$-module, and $\Omega_{L/k}$ is free of rank $1$ over $L$; $L$ is essentially of finite type over $k$; and there is a `CurveModel k L`, that is, an integral scheme $M.C$ with a proper morphism $M.\mathrm{toBase} \colon M.C \to \operatorname{Spec} k$ smooth of relative dimension $1$, a ring isomorphism $L \cong k(M.C)$ compatible with the map $k \to k(M.C)$ induced by $M.\mathrm{toBase}$, a bijection from the closed points of $M.C$ onto the places of $L/k$ under which the image of the stalk at a point in $L$ is exactly the corresponding valuation subring, and the property that every finite set of points of $M.C$ lies in a single affine open. Moreover there is an isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ with $e$ followed by the second projection equal to $M.\mathrm{toBase}$, so the model is identified with the base change of $c$ along $s$ as a scheme over $\operatorname{Spec} k$.
--
--   This packages a geometric fibre of a smooth proper relative curve as a model, in the project's sense, of its function field viewed as a one-variable function field over the algebraically closed residue field; it is the bridge from the scheme-theoretic hypotheses on $c$ to the divisor- and place-theoretic apparatus available for `CurveModel`. It is used in the construction of sections and theta-type sections in the relative Picard machinery, for instance by [`AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field`](thm.html#AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field) and [`AlgebraicGeometry.RelPicard.exists_thetaSection_ne_zero_and_stabilizer_trivial`](thm.html#AlgebraicGeometry.RelPicard.exists_thetaSection_ne_zero_and_stabilizer_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L) (_ : Algebra.EssFiniteType k L)
      (M : CurveModel k L) (e : M.C ≅ pullback c s), e.hom ≫ pullback.snd c s = M.toBase := by sorry
