-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/83979e36-c38f-5b63-b750-fbab1cc78367
-- title:
--   h⁰(Ω¹)=h¹(𝒪) for a smooth proper geometrically integral curve
-- statement:
--   Let $K$ be a field, $X$ a scheme, and $\mathcal V$ a two-chart affine open cover of $X$ in the sense of the project structure `Scheme.TwoAffineOpenCover`: two opens $U_0,U_1\subseteq X$, both affine, with $U_0\cap U_1$ affine and $U_0\cup U_1=X$. Let $c\colon X\to\operatorname{Spec}K$ be a morphism which is proper, smooth of relative dimension $1$, and satisfies the predicate `GeometricallyIntegral`. Write $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$ for the $K$-algebras of the associated two-chart Čech datum $\mathcal V.\mathrm{cover}\ c$, with the two restriction maps $\rho_0,\rho_1$ to $A_{01}$. For the Kähler sections, whose three modules are $\Omega_{A_0/K}$, $\Omega_{A_1/K}$, $\Omega_{A_{01}/K}$ with the maps induced by $\rho_0,\rho_1$, and for the structure-sheaf sections `lineBundle 1` of the same cover, the Čech differential of a `Sections` datum is $(m_0,m_1)\mapsto r_1(m_1)-r_0(m_0)$, $H^0$ is its kernel inside $M_0\times M_1$ and $H^1$ is $M_{01}$ modulo its range. The conclusion is the equality of $K$-dimensions $\operatorname{finrank}_K H^0(\mathcal V,\Omega^1)=\operatorname{finrank}_K H^1(\mathcal V,\mathcal O)$.
--
--   This is the equality $h^0(\Omega^1_{X/K})=h^1(\mathcal O_X)=g$ for a smooth proper geometrically integral curve over an arbitrary field, realised on a two-chart affine cover by Čech modules. It feeds the statement producing a free module of that rank together with its compatibility with base change, used to transport constancy of $h^1(\mathcal O)$ in a smooth proper family into constancy of $h^0(\Omega^1)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_kaehlerSections_H0_eq_finrank_structureSheafSections_H1_of_geometricallyIntegral
    {K : Type u} [Field K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] :
    Module.finrank K (𝒱.kaehlerSections c).H0 = Module.finrank K (𝒱.structureSheafSections c).H1 := by sorry
