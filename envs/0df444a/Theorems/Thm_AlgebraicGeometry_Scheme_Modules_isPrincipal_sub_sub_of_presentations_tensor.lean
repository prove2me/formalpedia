-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/97c262b5-961a-5a84-ad6b-834ad66aaece
-- title:
--   Tensor product of invertible sheaves adds divisors up to principal
-- statement:
--   Let $K$ be an algebraically closed field, and let $x \colon X \to \operatorname{Spec} K$ be a morphism from an integral scheme $X$, with $x$ proper and smooth of relative dimension $1$; the ring map [`AlgebraicCurve.baseToFunctionField x`](def/AlgebraicCurve_CurveModel.html#L18) makes the function field $X.\mathrm{functionField}$ a $K$-algebra, and divisors are finitely supported $\mathbb{Z}$-valued functions on the set of places of this extension, a place being a valuation subring $\neq F$ of the function field containing the image of $K$ and which is a principal ideal ring. Let $L$ and $L'$ be $\mathcal{O}_X$-modules, each satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ on which the pullback along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules. Let $D$, $D'$, $D''$ be divisors, and let $\varphi$, $\varphi'$, $\varphi''$ be families of additive maps $\Gamma(L,U) \to X.\mathrm{functionField}$, respectively for $L$, $L'$ and $L \otimes L'$, indexed by the opens $U$ of $X$, each family assumed: compatible with restriction to a nonempty smaller open; $\Gamma(X,U)$-semilinear, in the sense that $\varphi_U(a \cdot m) = \mathrm{algebraMap}(a)\,\varphi_U(m)$ for nonempty $U$; injective on nonempty opens; and, on every nonempty affine open $U$, with range exactly the $K$-subspace $\mathrm{lSpaceOn}$ of those $f$ in the function field satisfying $v(f) \le \exp(D v)$ for every place $v$ in $\mathrm{placesOf}\,x\,U$ (the places whose valuation subring is the image of the stalk at some closed point of $U$), with $D$ replaced by $D'$, resp. $D''$, for $\varphi'$, resp. $\varphi''$. The conclusion is that $D'' - D - D'$ is principal: there is a nonzero $f$ in the function field with $(D'' - D - D')(v) = v.\mathrm{ord}\,f$ for every place $v$.
--
--   This is the statement that the map $\operatorname{Pic} X \to \operatorname{Cl}(K(X))$ sending an invertible sheaf to the class of its divisor is additive, expressed in terms of presentations of invertible modules inside the constant sheaf of rational functions (such presentations exist by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn), and are unique up to a principal divisor by [`AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations)). It is used to construct the divisor class map for a curve model, to compute the Euler characteristic of a tensor product of invertible sheaves, and in the analysis of divisors on Néron models attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') := by sorry
