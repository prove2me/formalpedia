-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
-- name    : AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/c0ecd2a9-1034-5f9f-85db-b6d98679ad8f
-- title:
--   Two 𝒪(D)-presentations of a sheaf differ by a principal divisor
-- statement:
--   Let $K$ be an algebraically closed field and let $x\colon X\to\operatorname{Spec}K$ be a morphism with $X$ an integral scheme, $x$ proper and smooth of relative dimension $1$; the function field $X.\mathrm{functionField}$ is made a $K$-algebra by the germ at the generic point of the pullback of constants along $x$. Let $M$ be a sheaf of $\mathcal{O}_X$-modules, and let $D,D'$ be divisors, i.e. finitely supported integer-valued functions on the set of places of $K(X)$ over $K$ (valuation subrings of $K(X)$ containing $K$, distinct from $K(X)$, whose ring is a principal ideal ring). Let $\varphi_U,\varphi'_U\colon \Gamma(M,U)\to K(X)$ be additive maps, for $U$ ranging over the opens of $X$, such that each family commutes with restriction to nonempty opens, satisfies $\varphi_U(a\cdot m)=\mathrm{algebraMap}(a)\,\varphi_U(m)$ for $a\in\Gamma(X,U)$ and $U$ nonempty, is injective on nonempty opens, and, for every nonempty affine open $U$, has image exactly $\{f : v(f)\le \exp(D v)\ \text{for all places } v \text{ centred at a closed point of } U\}$, respectively the same set for $D'$; assume also that $M$ has a nonzero section over some open. Then there is $g\in K(X)$, $g\neq 0$, with $\varphi'_U(m)=g\,\varphi_U(m)$ for all nonempty $U$ and all $m\in\Gamma(M,U)$, with $D v=D' v+\operatorname{ord}_v(g)$ for every place $v$, and $D-D'$ principal, i.e. equal to the divisor of some nonzero element of $K(X)$.
--
--   This is the well-definedness of the divisor class attached to a module sheaf presented inside the constant sheaf of rational functions — the classical statement that the divisor of an invertible sheaf on a smooth proper curve is determined up to linear equivalence, giving the map $\operatorname{Pic}X\to\operatorname{Cl}X$. It is used to compare divisors arising from different presentations, for kernels of powers and for tensor products, and in the divisor computations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations.lean

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

theorem AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') := by sorry
