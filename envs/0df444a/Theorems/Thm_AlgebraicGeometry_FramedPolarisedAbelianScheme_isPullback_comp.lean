-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_comp
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/8522d64a-01a3-5e26-ba88-068afc4eb331
-- title:
--   Transitivity of base change for framed polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and commutative rings $S$, $S'$, $S''$, together with ring homomorphisms $\varphi : S \to S'$ and $\psi : S' \to S''$. Let $X$, $X'$, $X''$ be framed polarised abelian schemes of the given numerical type over $S$, $S'$, $S''$ respectively, i.e. polarised abelian schemes of relative dimension $g$, polarisation fibre rank $N+1$ and level $n$, each equipped with a projective presentation of the polarisation (a frame) whose associated map to $\mathbb{P}^N$ is a closed immersion and whose sections form a section basis. Assume `FramedPolarisedAbelianScheme.IsPullback` holds for $\varphi$ with $X$, $X'$ and for $\psi$ with $X'$, $X''$; that is, there is a morphism $g_{A} : X'.A \to X.A$ making the square with the structure morphisms and $\operatorname{Spec}\varphi$ cartesian, compatible with the relative group laws on all $T$-valued points, carrying the $2g$ level-$n$ sections of $X'$ to those of $X$, with $g_{A}^{*}$ of the polarisation of $X$ isomorphic to that of $X'$, and with the frame maps commuting with $\mathbb{P}^N_{S} \to \mathbb{P}^N_{S'}$; and similarly for $\psi$ with a morphism $X''.A \to X'.A$. The conclusion is that the same predicate holds for the composite $\psi \circ \varphi$ with $X$ and $X''$.
--
--   This is the transitivity (composability) of base change for framed polarised abelian schemes: the relation "$X'$ is the base change of $X$ along $\varphi$" composes along a tower $S \to S' \to S''$. It is used where invariants of framed polarised abelian schemes are defined through base changes, notably in the statements on reframing over a cover and on the ideal cutting out the theta-adapted locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_comp.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_comp
    {g N n : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S')
    (X'' : FramedPolarisedAbelianScheme g N n S'')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X X') (h' : FramedPolarisedAbelianScheme.IsPullback ψ X' X'') :
    FramedPolarisedAbelianScheme.IsPullback (ψ.comp φ) X X'' := by sorry
