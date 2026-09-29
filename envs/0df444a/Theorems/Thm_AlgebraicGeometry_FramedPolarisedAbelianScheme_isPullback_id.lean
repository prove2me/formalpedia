-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_id
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/13e77257-3e35-5f08-9835-37932ea034b5
-- title:
--   Reflexivity of base change along id_S for framed polarised abelian schemes
-- statement:
--   Let $g$, $N$, $n$ be natural numbers, let $S$ be a commutative ring, and let $X$ be a framed polarised abelian scheme of type $(g, N+1, n)$ over $S$, that is: a polarised abelian scheme consisting of a scheme $X.A$ with a structure morphism $X.f : X.A \to \operatorname{Spec} S$, a commutative relative group law $X.L$, the property bundle, fibres of topological Krull dimension $g$, sections $X.P_i$ ($i < 2g$) that are $n$-torsion and form a basis of the geometric $n$-torsion, an invertible module $X.pol$ with the stated very-ampleness and geometric $h^0$ conditions, together with a frame: a projective presentation of $X.pol$ relative to $X.f$ by $N+1$ global sections whose associated morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis. The assertion is that $X$ is a base change of itself along the identity ring homomorphism of $S$, i.e. there exist a morphism $gA : X.A \to X.A$ and a proof that the square formed by $gA$, $X.f$, $X.f$ and $\operatorname{Spec}$ of the identity is cartesian, such that: $gA$ is compatible with the relative group law on all $T$-points over any $t' : T \to \operatorname{Spec} S$; $(X.P_i).1 \circ gA$ equals $(X.P_i).1$ precomposed with $\operatorname{Spec}$ of the identity, for each $i$; the pullback of $X.pol$ along $gA$ is isomorphic to $X.pol$; and the frame morphism followed by the base-change map $\mathbb{P}^N_S \to \mathbb{P}^N_S$ along the identity agrees with $gA$ followed by the frame morphism.
--
--   This is the reflexivity clause for the base-change relation on framed polarised abelian schemes: the relation $\mathrm{IsPullback}$ holds for the identity homomorphism of the base ring. It is used where a construction defined on base changes has to be evaluated on the object itself, as in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_isThetaAdapted_iff_eq_bot`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_isThetaAdapted_iff_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isPullback_id.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_id
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) :
    FramedPolarisedAbelianScheme.IsPullback (RingHom.id S) X X := by sorry
