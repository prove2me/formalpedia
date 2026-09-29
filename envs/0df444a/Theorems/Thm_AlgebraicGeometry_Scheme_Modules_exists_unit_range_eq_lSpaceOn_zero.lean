-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
-- name    : AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d16a69cb-6f44-5d22-86fe-88a34cc4c095
-- title:
--   Structure sheaf as L_{S_U}(0) inside the function field
-- statement:
--   Let $K$ be a field, $X$ a scheme, and $x\colon X\to\operatorname{Spec} K$ a morphism with $X$ integral and $x$ smooth of relative dimension $1$; the ring homomorphism [`AlgebraicCurve.baseToFunctionField x`](def/AlgebraicCurve_CurveModel.html#L18), namely $x$ on global sections followed by the germ at the generic point, makes the function field $K(X)=$ `X.functionField` a $K$-algebra. The assertion is the existence of a family of additive maps $\varphi_U\colon \Gamma(U,\mathcal O_X)\to K(X)$, indexed by the open sets $U$ of $X$ and defined on the sections over $U$ of the unit module `SheafOfModules.unit X.ringCatSheaf` over the sheaf of rings of $X$, with five properties: for nonempty $U$, $\varphi_U$ is the germ map `X.germToFunctionField U` applied to the section regarded as an element of $\Gamma(X,U)$; for $V\le U$ with $V$ nonempty, $\varphi_V$ of the restriction of $m$ equals $\varphi_U(m)$; for nonempty $U$, $a\in\Gamma(X,U)$ and $m$, one has $\varphi_U(a\cdot m)=\varphi_U(m)$ times the image of $a$ under $\Gamma(X,U)\to K(X)$; $\varphi_U$ is injective for nonempty $U$; and for every nonempty affine open $U$ the image of $\varphi_U$ is exactly $L_{S_U}(0)$, the set of $f\in K(X)$ with $v(f)\le 1$ for the adic valuation of every place $v$ of $K(X)/K$ (a valuation subring containing $K$, not all of $K(X)$, and a principal ideal ring) whose valuation subring is the image of the stalk of $X$ at some closed point lying in $U$. No condition is imposed on $\varphi_U$ for empty $U$.
--
--   This is the identification of the structure sheaf of a smooth integral curve over $K$ with the subsheaf $\mathcal O(0)$ of the constant sheaf $K(X)$, the sections over an affine open being the rational functions with no pole at the places centred in that open. It feeds the computations of Euler characteristics of invertible modules and the construction of the divisor class map in the curve-model development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+ (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) := by sorry
