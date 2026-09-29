-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_of_isReframe
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_of_isReframe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/9f0b0b49-3757-5ffc-9f88-65c4d4f673a4
-- title:
--   Reframing commutes with base change
-- statement:
--   Let $g,N,n$ be natural numbers, let $S,S'$ be commutative rings, let $\varphi : S \to S'$ be a ring homomorphism and let $U$ be an $(N+1)\times(N+1)$ matrix over $S$. Let $X,X'$ be framed polarised abelian schemes of type $(g,N,n)$ over $S$ and $Y,Y'$ such data over $S'$; recall that such an object consists of a polarised abelian scheme $A \to \operatorname{Spec} S$ of relative dimension $g$ with $n$-torsion level data and an invertible polarisation sheaf with geometric $H^0$-rank $N+1$, together with a `ProjPresentation` (global sections $\sigma_0,\dots,\sigma_N$ of the polarisation sheaf and a morphism to $\mathbb{P}^N$ over the base) whose associated morphism to $\mathbb{P}^N$ is a closed immersion and whose sections form a section basis. Assume `FramedPolarisedAbelianScheme.IsPullback φ X Y`, i.e. there is $g_A : Y.A \to X.A$ making the square over $\operatorname{Spec}\varphi$ cartesian, compatible with the relative group laws and with the marked torsion sections, an isomorphism between the $g_A$-pullback of $X$'s polarisation sheaf and $Y$'s, and the frame identity $\iota_{Y}$ followed by $\mathbb{P}^N_{S'} \to \mathbb{P}^N_{S}$ equals $g_A$ followed by $\iota_X$. Assume further that $X'$ is obtained from $X$ by reframing along $U$ (same underlying polarised abelian scheme, frame given by a presentation whose sections are $\sigma'_i = \sum_j U_{ij}\sigma_j$, with the scalars taken in $\Gamma(X.A,\top)$ via the structure morphism), and that $Y'$ is obtained from $Y$ by reframing along the entrywise image $\varphi(U)$. Then `FramedPolarisedAbelianScheme.IsPullback φ X' Y'`.
--
--   The statement records that the reframing operation on framed polarised abelian schemes, which replaces a projective frame by its $U$-transform, is compatible with base change along a ring homomorphism, so that the moduli-theoretic base-change relation is preserved. It is used in the construction of coverings by reframed charts and in the analysis of the finite group action on theta-adapted frames.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_of_isReframe.lean

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_of_isReframe
    {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S)
    (X X' : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X Y) (hX : X.IsReframe U X') (hY : Y.IsReframe (U.map φ) Y') :
    FramedPolarisedAbelianScheme.IsPullback φ X' Y' := by sorry
