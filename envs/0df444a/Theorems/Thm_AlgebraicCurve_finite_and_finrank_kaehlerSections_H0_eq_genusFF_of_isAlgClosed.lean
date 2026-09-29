-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed
-- name    : AlgebraicCurve.finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/54105365-f176-5acc-a794-4b4d39a7be1d
-- title:
--   Čech H⁰ of Ω¹ on a two-chart cover equals the genus
-- statement:
--   Let $K$ be an algebraically closed field and $C$ a scheme, equipped with a `TwoAffineOpenCover` $\mathcal V$, that is: two opens $U_0, U_1$ of $C$, each affine, with affine intersection $U_0 \sqcap U_1$ and with $U_0 \sqcup U_1 = \top$. Let $c : C \to \operatorname{Spec} K$ be a morphism, and assume $C$ is integral, $c$ is proper and $c$ is smooth of relative dimension $1$. The function field $C.\mathrm{functionField}$ is regarded as a $K$-algebra through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the ring homomorphism obtained by composing the identification $K \cong \Gamma(\operatorname{Spec} K)$, the map $c^\sharp$ on global sections, and the germ at the generic point of $C$. The assertion is that the $K$-module $(\mathcal V.\mathrm{kaehlerSections}\ c).H_0$ — the kernel of the Čech differential $(\omega_0,\omega_1) \mapsto -r_0\omega_0 + r_1\omega_1$ from $\Omega_{\Gamma(C,U_0)/K} \times \Omega_{\Gamma(C,U_1)/K}$ to $\Omega_{\Gamma(C,U_0 \sqcap U_1)/K}$, the maps $r_0, r_1$ being induced by the two restrictions — is a finite $K$-module, and that its $K$-rank equals [`AlgebraicCurve.genusFF K C.functionField`](def/AlgebraicCurve_Repartitions.html#L145), the $K$-dimension of the répartition space $H^1$ of the zero divisor of the function field $C.\mathrm{functionField}$ over $K$.
--
--   This is the identification $h^0(C, \Omega^1_{C/K}) = g$ for a smooth proper integral curve over an algebraically closed field, with the genus taken in the répartition (adelic) normalisation of the function field, and with global $1$-forms computed as the Čech $H^0$ of a two-chart affine cover. Together with the corresponding computation for the structure sheaf it yields the comparison $h^0(\Omega^1) = h^1(\mathcal O_C)$, and it is used in the proof that these two ranks agree for geometrically integral curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.finite_and_finrank_kaehlerSections_H0_eq_genusFF_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.kaehlerSections c).H0 ∧
      Module.finrank K (𝒱.kaehlerSections c).H0 = AlgebraicCurve.genusFF K C.functionField := by sorry
