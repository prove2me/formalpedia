-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow
-- name    : AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/1203ead1-3a04-5485-93dd-28901618917f
-- title:
--   Divisor of mathcal I_P^{ n} and its dual at a point
-- statement:
--   Let $K$ be an algebraically closed field, $X$ an integral scheme and $x\colon X\to\operatorname{Spec}K$ a proper morphism, smooth of relative dimension $1$; let $P\colon\operatorname{Spec}K\to X$ be a section of $x$ (so $P$ followed by $x$ is the identity), let $n\in\mathbb N$, and regard $K(X)=X.\text{functionField}$ as a $K$-algebra via [`AlgebraicCurve.baseToFunctionField`](def/AlgebraicCurve_CurveModel.html#L18). Let $v$ be a place of $K(X)/K$ in the sense of the project (a valuation subring of $K(X)$, distinct from $K(X)$, containing the image of $K$ and a principal ideal ring) whose valuation subring is the image of the stalk of $X$ at the image point $P(\text{closed point})$ inside $K(X)$. Let $D,D'$ be divisors, i.e. finitely supported $\mathbb Z$-valued functions on places. Assume given, for every open $U\subseteq X$, additive maps $\varphi_U$ on the sections over $U$ of the dual $((\mathcal I_P^{\,n})^{\vee}$, written `(P.ker ^ n).invModule`$)$ and $\varphi'_U$ on those of the ideal sheaf module `(P.ker ^ n).module`, both taking values in $K(X)$, compatible with restriction to nonempty opens, semilinear for the action of $\Gamma(X,U)$ via $\Gamma(X,U)\to K(X)$, injective over nonempty opens, and with ranges over nonempty affine opens $U$ equal to $\{f : w(f)\le\exp(D(w))$ for all places $w$ centred at closed points of $U\}$, respectively the same set for $D'$. Then $D-n\,[v]$ and $D'+n\,[v]$ are principal, i.e. each is the divisor $w\mapsto \operatorname{ord}_w(f)$ of some $f\in K(X)^{\times}$.
--
--   This identifies the divisor classes of $\mathcal O_X(nP)=(\mathcal I_P^{\,n})^{\vee}$ and $\mathcal O_X(-nP)=\mathcal I_P^{\,n}$ on a smooth proper curve as $n[v]$ and $-n[v]$, where $v$ is the place centred at the $K$-point $P$, expressed through presentations of these modules inside the function field. It feeds the construction of the divisor class map for the project's curve model and the computation of divisors attached to the Poincaré bundle pulled back along sections in the modular-curve development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow.lean

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

theorem AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) := by sorry
