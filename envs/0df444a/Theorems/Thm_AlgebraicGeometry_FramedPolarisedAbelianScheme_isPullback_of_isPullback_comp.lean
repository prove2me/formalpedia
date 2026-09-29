-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_comp
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/46be9364-e517-5e09-9e87-21752d12b2d9
-- title:
--   Cancellation of framed base-change squares
-- statement:
--   Let $g,N,n$ be natural numbers, let $S,S',S''$ be commutative rings, and let $\varphi : S \to S'$ and $\psi : S' \to S''$ be ring homomorphisms. Let $X$, $X'$, $X''$ be framed polarised abelian schemes with parameters $g$, $N$, $n$ over $S$, $S'$, $S''$ respectively, each consisting of a polarised abelian scheme (abelian scheme $A \to \operatorname{Spec}$ of the base, with commutative relative group law, $2g$ sections of $n$-torsion forming a basis of the geometric $n$-torsion, and an invertible very ample sheaf of geometric fibre degree $N+1$) together with a projective frame: $N+1$ global sections of the polarisation, a morphism to $\mathbb{P}^N$ over the base that is a closed immersion and whose sections form a section basis. Assume `FramedPolarisedAbelianScheme.IsPullback` holds for $\psi \circ \varphi$ between $X$ and $X''$, and for $\varphi$ between $X$ and $X'$; that is, in each case there is a morphism of total spaces making the square over $\operatorname{Spec}$ of the base map cartesian, compatible with the group laws and with the marked torsion sections, pulling back the polarisation to the polarisation up to isomorphism, and compatible with the frames via the map $\mathbb{P}^N$ over the base change. Then the same holds for $\psi$ between $X'$ and $X''$.
--
--   This is the left cancellation property for base change of framed polarised abelian schemes: given that $X''$ is the base change of $X$ along $\psi \circ \varphi$ and $X'$ the base change along $\varphi$, then $X''$ is the base change of $X'$ along $\psi$. It is the framed counterpart of the corresponding statement for polarised abelian schemes, and is used in the analysis of the ideal governing when a framed polarised abelian scheme descends along a base change ([`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_translate_comp_eq_iff_map_eq_bot`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_exists_translate_comp_eq_iff_map_eq_bot)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_of_isPullback_comp.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_comp
    {g N n : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S')
    (X'' : FramedPolarisedAbelianScheme g N n S'')
    (h : FramedPolarisedAbelianScheme.IsPullback (ψ.comp φ) X X'') (h₁ : FramedPolarisedAbelianScheme.IsPullback φ X X') :
    FramedPolarisedAbelianScheme.IsPullback ψ X' X'' := by sorry
