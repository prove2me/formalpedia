-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ff48962c-f08a-5322-93cc-0378f976d0d7
-- title:
--   Tangent coordinates are stable under postcomposition with ψ
-- statement:
--   Let $T'$ be a local ring in universe $u$, $I\subseteq T'$ an ideal, and $V$ an abelian group carrying compatible left and right module structures over the residue field $k=\mathrm{ResidueField}\,T'$ (central scalars) together with a $T'$-module structure forming a scalar tower over $k$; let $\iota\colon V\to T'$ be $T'$-linear and $C$ a $T'$-algebra. Given schemes $Y,Y'$, a morphism $\psi\colon Y\to Y'$, two points $u,v\colon \operatorname{Spec} C\to Y$, a scheme $A_k$ with structure morphism $x_k\colon A_k\to\operatorname{Spec} k$ and a `RelativeGroupLaw` $L_k$ for $x_k$ (a functorial group structure on the sets of $x_k$-sections over arbitrary $k$-schemes), opens $W\le W'$ and $U_e$ of $A_k$, morphisms $a_W\colon W\to Y$ and $a_{W'}\colon W'\to Y'$ satisfying $(W\hookrightarrow W')\gg a_{W'}=a_W\gg\psi$, and a function $c$ from $\Gamma(A_k,U_e)$ to $k$-linear maps $V^{*}\to k\otimes_{T'}C$: if $c$ is a system of tangent coordinates for the pair $(u,v)$ via $(W,a_W)$ at $U_e$ — that is, there are $w_0\colon \operatorname{Spec}(\text{thickening})\to W$ with $(w_0\gg W.\iota)\gg x_k$ the standard base morphism, and $w_1\colon \operatorname{Spec}(\text{thickening})\to U_e$, such that $w_0\gg a_W$ is a tangent morphism for $(u,v)$ (it factors as $\operatorname{Spec}\vartheta\gg\varphi$ for a Schlessinger map $\vartheta$ on the pair ring and a $\varphi$ restricting to $u$ and $v$ along the two projections), $w_1$ lies over the $L_k$-translate of $w_0\gg W.\iota$ to the identity section, and $c$ is the tangent-coordinate function of the chart ring homomorphism of $w_1$ — then the very same $c$ is a system of tangent coordinates for the pair $(u\gg\psi,v\gg\psi)$ via $(W',a_{W'})$ at $U_e$. No hypothesis on $\psi$ beyond the compatibility $(W\hookrightarrow W')\gg a_{W'}=a_W\gg\psi$ is imposed.
--
--   This is a transport lemma for the project's relation of being tangent coordinates of a pair via a local chart: it allows the chart datum $(W,a_W)$ to be enlarged to $(W',a_{W'})$ and the target to be changed along a morphism extending the comparison map, without altering the coordinate function. It is used when transition isomorphisms between local lifts are applied to move the values of the obstruction cochain into a common target, and feeds the statements about the resulting two-cochain, its defect and its coboundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y Y' : Scheme.{u}} (ψ : Y ⟶ Y') (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W W' : Ak.Opens) (hWW : W ≤ W') (aW : (W : Scheme.{u}) ⟶ Y) (aW' : (W' : Scheme.{u}) ⟶ Y')
    (haW : Ak.homOfLE hWW ≫ aW' = aW ≫ ψ) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c) :
    IsTangentCoordsOfPairAtVia I V ι C (u ≫ ψ) (v ≫ ψ) xk Lk W' aW' Ue c := by sorry
