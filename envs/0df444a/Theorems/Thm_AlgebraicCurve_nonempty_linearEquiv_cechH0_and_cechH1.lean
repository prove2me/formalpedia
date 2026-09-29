-- Prove2me | Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
-- name    : AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/b3bd13fd-c307-56c7-90f0-2a8ce3b67063
-- title:
--   Čech cohomology of mathcal O_C computed by places
-- statement:
--   Let $K$ be a field, $C$ a scheme, and $c : C \to \operatorname{Spec} K$ a morphism; assume $C$ is integral, $c$ is separated and smooth of relative dimension $1$. Let $\mathcal V$ be a two-affine open cover of $C$, i.e. opens $U_0,U_1$ with $U_0,U_1$ and $U_0\cap U_1$ affine and $U_0\sqcup U_1=\top$, and assume $U_0$ and $U_1$ are nonempty. Give $C.\mathrm{functionField}$ the $K$-algebra structure coming from [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the germ at the generic point of the map on global sections induced by $c$. Write $S_i$ for `placesOf c U_i`: the set of places $v$ of $C.\mathrm{functionField}$ over $K$ (valuation subrings containing $K$, not the whole field, principal ideal rings) for which some closed point $x \in U_i$ has $\operatorname{im}(\mathcal O_{C,x} \to C.\mathrm{functionField})$ equal to the valuation subring of $v$. The assertion is that both of the following types are nonempty: the type of $K$-linear isomorphisms from $\ker\bigl(\Gamma(C,U_0)\times\Gamma(C,U_1)\to\Gamma(C,U_0\cap U_1)\bigr)$ onto $\ker\bigl(L_{S_0}(0)\times L_{S_1}(0)\to L_{S_0\cap S_1}(0)\bigr)$, and the type of $K$-linear isomorphisms from the cokernel $\Gamma(C,U_0\cap U_1)/\mathrm{im}$ onto $L_{S_0\cap S_1}(0)/\mathrm{im}$, where $L_S(0)=\{f : v(f)\le 1 \text{ for all } v\in S\}$ and the maps are the two-chart Čech differentials at the zero divisor.
--
--   This is the dictionary between the Čech complex of the structure sheaf on a two-chart affine cover of a smooth curve and the complex of rational functions without poles on each chart, in degrees $0$ and $1$. It is used to transport finiteness of $H^0$ and $H^1$ of the structure sheaf of a smooth proper curve, and the Riemann–Roch style nonvanishing and vanishing statements for sections of invertible modules, between the scheme-theoretic and function-field settings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1 {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Nonempty ((𝒱.structureSheafSections c).H0 ≃ₗ[K]
        ↥(AlgebraicCurve.cechH0 (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1)
            (0 : AlgebraicCurve.Divisor K C.functionField))) ∧
      Nonempty ((𝒱.structureSheafSections c).H1 ≃ₗ[K]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf c 𝒱.U0) (AlgebraicCurve.placesOf c 𝒱.U1)
            (0 : AlgebraicCurve.Divisor K C.functionField)) := by sorry
