-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/500442da-8194-534c-871e-6cbe92b6d3ef
-- title:
--   Čech global 1-forms are regular differentials
-- statement:
--   Let $k$ be a perfect field, $X$ a scheme, and $\mathcal{V}$ a two-chart affine open cover of $X$, i.e. a pair of opens $U_0, U_1$, each affine, with affine intersection and $U_0 \sqcup U_1 = \top$. Let $c : X \to \operatorname{Spec} k$ be a morphism, and assume $X$ is integral, $c$ is proper and smooth of relative dimension $1$, and both $U_0$ and $U_1$ are nonempty. The sections of $\Omega^1$ for this cover are the triple of Kähler modules $\Omega[\Gamma(X,U_0)/k]$, $\Omega[\Gamma(X,U_1)/k]$, $\Omega[\Gamma(X,U_0 \sqcap U_1)/k]$ (the $k$-algebra structures coming from $c$ via `algebraOfHom`) together with the two restriction maps, and $\omega$ is an element of the degree-zero Čech cohomology of this datum, i.e. a pair $(\omega_0,\omega_1)$ in the kernel of $(-r_0) \oplus r_1$, so that $\omega_0$ and $\omega_1$ have the same restriction to $U_0 \sqcap U_1$. Giving $X.\text{functionField}$ the $k$-algebra structure induced by `baseToFunctionField c` (the germ at the generic point of the global sections pulled back along $c$), the conclusion is that the image of $\omega_0$ under `kaehlerToFunctionField c 𝒱.U0`, the map $\Omega[\Gamma(X,U_0)/k] \to \Omega[X.\text{functionField}/k]$ induced by the germ homomorphism at the generic point, lies in `regularDifferentials k X.functionField`: for every place $v$ of $X.\text{functionField}$ over $k$ (a valuation subring, not all of the field, containing the image of $k$ and a principal ideal ring) there exists $f$ in the valuation subring of $v$ with that image equal to $f \cdot v.\mathrm{dCoord}$.
--
--   This identifies Čech global sections of $\Omega^1_{X/k}$ on a two-chart affine cover of a smooth proper curve with regular differentials of the function field, the bridge between the scheme-theoretic and the function-field descriptions of $H^0(X,\Omega^1)$. It is used in the construction of the comparison isomorphism between $\check{H}^0(\mathcal{V},\Omega^1)$ and $\Omega_{\mathrm{reg}}$, in the Serre-pairing comparisons, and in the treatment of differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1]
    (ω : (𝒱.kaehlerSections c).H0) :
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c 𝒱.U0 ω.val.1 ∈ regularDifferentials k X.functionField := by sorry
