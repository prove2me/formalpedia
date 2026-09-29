-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
-- name    : AlgebraicGeometry.isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/744b6b87-09fe-5b98-9f1b-c9fc2cb14b83
-- title:
--   Residue field map is an isomorphism at a κ(y)-valued point
-- statement:
--   Let $X$ and $Y$ be schemes in the lowest universe, let $f \colon X \to Y$ be a morphism of schemes, and let $y$ be a point of (the underlying space of) $Y$. Let $u_0 \colon \operatorname{Spec}\kappa(y) \to X$ be a morphism from the spectrum of the residue field `Y.residueField y` of $Y$ at $y$, and assume that $u_0$ followed by $f$ equals the canonical morphism `Y.fromSpecResidueField y`, i.e. $f \circ u_0$ is the canonical morphism $\operatorname{Spec}\kappa(y) \to Y$ with image $y$. Write $x := u_0(\mathfrak{m})$ for the image under the underlying continuous map of $u_0$ of the closed point of $\operatorname{Spec}\kappa(y)$, i.e. of `IsLocalRing.closedPoint` of the local (indeed, field) ring `Y.residueField y`. The conclusion is that the ring homomorphism `f.residueFieldMap x`, the induced map $\kappa(f(x)) \to \kappa(x)$ on residue fields at $x$, is an isomorphism in the category of commutative rings.
--
--   This is the standard statement that a point of $X$ carrying a $\kappa(y)$-valued point of the fibre $X_y$ is $\kappa(y)$-rational: its residue field is, via $f$, the residue field of $y$. It is used in the treatment of models of modular curves, where rationality of a distinguished point of a base change is needed, via [`ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq`](thm.html#ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_residueFieldMap_of_comp_eq_fromSpecResidueField
    {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y) (u₀ : Spec (Y.residueField y) ⟶ X)
    (hu₀ : u₀ ≫ f = Y.fromSpecResidueField y) :
    IsIso (f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) := by sorry
