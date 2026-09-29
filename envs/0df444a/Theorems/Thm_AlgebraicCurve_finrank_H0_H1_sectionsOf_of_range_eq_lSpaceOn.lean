-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn
-- name    : AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0adca9ef-d173-54bf-918c-f7b84b09e98a
-- title:
--   Riemann–Roch in two-chart Čech form for 𝒪(D)
-- statement:
--   Let $K$ be an algebraically closed field and $X$ a scheme over $K$ via $x \colon X \to \operatorname{Spec} K$, with $X$ integral, $x$ proper and smooth of relative dimension $1$; let $\mathcal{V}$ be a two-chart affine cover of $X$, i.e. affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine, and let $M$ be a sheaf of modules on $X$. Regard the function field $X.\mathrm{functionField}$ as a $K$-algebra via [`AlgebraicCurve.baseToFunctionField x`](def/AlgebraicCurve_CurveModel.html#L18) (the germ at the generic point of the map on global sections), and let $D$ be a divisor, i.e. a finitely supported $\mathbb{Z}$-valued function on the places of $X.\mathrm{functionField}/K$. Assume given additive maps $\varphi_U \colon \Gamma(M,U) \to X.\mathrm{functionField}$ for all opens $U$ such that: $\varphi_V \circ \mathrm{res}_{V \le U} = \varphi_U$ whenever $V$ is nonempty; $\varphi_U(a \cdot m) = \mathrm{algebraMap}(a)\,\varphi_U(m)$ for $a \in \Gamma(X,U)$ and $U$ nonempty; $\varphi_U$ is injective for $U$ nonempty; and for $U$ nonempty affine the image of $\varphi_U$ is exactly $\{f : v(f) \le \exp(D v) \text{ for all } v \in \mathrm{placesOf}\,x\,U\}$, where $\mathrm{placesOf}\,x\,U$ is the set of places whose valuation subring is the image of the stalk at some closed point of $U$. Then, for the two-chart Čech complex of $M$ along $\mathcal{V}$ over $K$ — with $H^0$ the kernel of the difference of restrictions $\Gamma(M,U_0) \times \Gamma(M,U_1) \to \Gamma(M,U_0 \sqcap U_1)$ and $H^1$ its cokernel — both $H^0$ and $H^1$ are finite $K$-modules, $\dim_K H^0 = \ell(D)$ (the dimension of the Riemann–Roch space of $D$), $\dim_K H^1 = i(D)$ (the index of speciality, the $K$-dimension of the adele space modulo the sum of the $D$-bounded and the principal adeles), and $\dim_K H^0 - \dim_K H^1 = \deg D + 1 - g$, where $\deg D = \sum_v D(v)\deg v$ and $g$ is the genus of $X.\mathrm{functionField}/K$ defined as the $K$-dimension of the repartition quotient at the zero divisor.
--
--   This is the Riemann–Roch theorem for an invertible sheaf presented as $\mathcal{O}(D)$ inside the function field, stated in the currency of two-chart Čech cohomology and with no further hypotheses beyond $K = \bar K$ and properness and smoothness of the curve. It supplies the numerical input ($h^0$, $h^1$ and the Euler characteristic) for the curve-model and relative Picard constructions that cite it, for instance in recognising when the Čech $H^0$ of a module forces it to be trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules)
    (D : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    Module.Finite K (𝒱.sectionsOf x M).H0 ∧ Module.Finite K (𝒱.sectionsOf x M).H1 ∧
      Module.finrank K (𝒱.sectionsOf x M).H0 = AlgebraicCurve.ell D ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = AlgebraicCurve.indexOfSpecialty D ∧
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1
        = AlgebraicCurve.Divisor.degree D + 1 - AlgebraicCurve.genusFF K X.functionField := by sorry
