-- Prove2me | Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
-- name    : AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/75c781f6-353c-5eb5-9e0f-5c2c63587d58
-- title:
--   Two-chart Čech cohomology of a module realised as L(D)
-- statement:
--   Let $K$ be a field, $X$ a scheme with a structure morphism $x \colon X \to \operatorname{Spec} K$, and assume $X$ is integral and $x$ is separated and smooth of relative dimension $1$. Let $\mathcal V$ be a two-chart affine open cover of $X$, that is, affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine, and assume $U_0$ and $U_1$ are nonempty. Let $M$ be a sheaf of $\mathcal O_X$-modules and let $D$ be a divisor of $X.\mathrm{functionField}$ over $K$, i.e. a finitely supported integer-valued function on the places $v$ of the function field (valuation subrings, proper, containing the image of $K$ under `baseToFunctionField`, and principal ideal rings), the $K$-algebra structure on the function field being the one induced by $x$. Suppose given additive maps $\varphi_U \colon \Gamma(M,U) \to X.\mathrm{functionField}$, one for each open $U$, such that: $\varphi_V$ composed with restriction $\Gamma(M,U) \to \Gamma(M,V)$ equals $\varphi_U$ whenever $V \le U$ and $V$ is nonempty; $\varphi_U(a \cdot m) = \operatorname{algebraMap}(a)\,\varphi_U(m)$ for $a \in \Gamma(X,U)$, $m \in \Gamma(M,U)$ and $U$ nonempty; $\varphi_U$ is injective for $U$ nonempty; and for every nonempty affine open $U$ the range of $\varphi_U$ is the $K$-submodule $L_{S_U}(D) = \{f : v(f) \le \exp(D(v)) \text{ for all } v \in S_U\}$, where $S_U = \mathrm{placesOf}(x,U)$ is the set of places whose valuation subring is the image of the stalk at some closed point of $U$ inside the function field, and $v$ denotes the adic valuation. The conclusion is that both types of $K$-linear equivalences below are nonempty: $(\mathcal V.\mathrm{sectionsOf}\ x\ M).H_0$, the kernel of the difference-of-restrictions map $\Gamma(M,U_0) \times \Gamma(M,U_1) \to \Gamma(M,U_0 \sqcap U_1)$, is isomorphic to the kernel of $L_{S_{U_0}}(D) \times L_{S_{U_1}}(D) \to L_{S_{U_0} \cap S_{U_1}}(D)$, and $(\mathcal V.\mathrm{sectionsOf}\ x\ M).H_1$, the cokernel of the former map, is isomorphic to the cokernel of the latter; thus isomorphisms are asserted to exist, with no canonical choice specified.
--
--   This is the comparison, for a curve covered by two affine charts, between the two-chart Čech cohomology of a module sheaf presented as the sheaf $\mathcal O(D)$ inside the constant sheaf of rational functions and the Čech complex of $L(D)$-spaces formed inside the function field. It feeds the computation of the $K$-dimensions of $H^0$ and $H^1$ in [`AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn`](thm.html#AlgebraicCurve.finrank_H0_H1_sectionsOf_of_range_eq_lSpaceOn), and the variant [`AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf`](thm.html#AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf) in which the divisor and the maps $\varphi_U$ are produced rather than assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
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

theorem AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
    {K : Type u} [Field K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [SmoothOfRelativeDimension 1 x]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) (M : X.Modules)
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
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[K]
        ↥(AlgebraicCurve.cechH0 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D)) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[K]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D) := by sorry
