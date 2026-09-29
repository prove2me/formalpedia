-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
-- name    : AlgebraicGeometry.eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/ee70fd3b-38e1-574c-9ed5-a83ebfa4d14c
-- title:
--   Uniqueness of K-points over a point with isomorphic residue field
-- statement:
--   Let $K$ be a field, let $X$ and $Y$ be schemes (all in one universe), and let $f \colon X \to Y$ be a morphism of schemes. Let $u, u' \colon \operatorname{Spec}(K) \to X$ be two morphisms, where $K$ is regarded as a commutative ring via `CommRingCat.of`. Assume: first, that $u$ followed by $f$ equals $u'$ followed by $f$, i.e. $f \circ u = f \circ u'$ as morphisms $\operatorname{Spec}(K) \to Y$; second, that the two underlying continuous maps send the closed point of $\operatorname{Spec}(K)$ (the closed point of the local ring $K$) to the same point $x_0$ of $X$; and third, that the induced map on residue fields $f.\mathrm{residueFieldMap}(x_0) \colon \kappa(f(x_0)) \to \kappa(x_0)$ is an isomorphism, where $x_0$ is written as the image of the closed point under $u$. The conclusion is that $u = u'$ as morphisms of schemes.
--
--   This is the standard description of $K$-valued points of a scheme — a point together with a field embedding of its residue field into $K$ — used to separate two such points that agree over $Y$; the residue-field hypothesis is what holds, for instance, when $f$ is unramified at $x_0$ with trivial residue extension. It is used in the project for uniqueness of sections of smooth morphisms of relative dimension one and for the corresponding rigidity statement about sections of a model of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : X ⟶ Y) (u u' : Spec (CommRingCat.of K) ⟶ X) (h : u ≫ f = u' ≫ f)
    (hpt : u.base (IsLocalRing.closedPoint K) = u'.base (IsLocalRing.closedPoint K))
    (hκ : IsIso (f.residueFieldMap (u.base (IsLocalRing.closedPoint K)))) :
    u = u' := by sorry
