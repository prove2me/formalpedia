-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isPullback_of_isPullback
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/365e715c-f3e2-5b4a-a68c-427aa112b286
-- title:
--   Framed base change is unique up to framed isomorphism
-- statement:
--   Fix natural numbers $g$, $N$, $n$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$. Let $X$ be a framed polarised abelian scheme of the project's type over $S$, that is, a polarised abelian scheme $(A_X \to \operatorname{Spec} S, L_X, P_X, \mathcal L_X)$ with invariant $d = N+1$ and $n$-torsion frame data, together with a projective presentation `frame` of $\mathcal L_X$ over $\mathbb P^N_S$ whose structural map is a closed immersion and whose sections form a section basis; and let $Y$, $Y'$ be two such objects over $S'$ with the same $g$, $N$, $n$. Assume both $Y$ and $Y'$ are base changes of $X$ along $\varphi$ in the sense of `FramedPolarisedAbelianScheme.IsPullback`: for each there is a morphism $g_A$ to $A_X$ making the square with the structure morphisms and $\operatorname{Spec}\varphi$ cartesian, compatible with the relative group laws on points over arbitrary bases, carrying the $2g$ marked $n$-torsion sections to the corresponding sections of $X$ composed with $\operatorname{Spec}\varphi$, admitting an isomorphism $g_A^{*}\mathcal L_X \cong \mathcal L$, and satisfying $\iota \,;\, (\mathbb P^N_{S'} \to \mathbb P^N_S) = g_A \,;\, \iota_X$ on the frame morphisms. The conclusion is `FramedPolarisedAbelianScheme.Iso` $Y$ $Y'$: there is an isomorphism $e : A_Y \cong A_{Y'}$ over $\operatorname{Spec} S'$ which respects the frame morphisms to $\mathbb P^N_{S'}$, is a homomorphism for the relative group laws on points over any base, matches the $2g$ marked sections, and for every point of $\operatorname{Spec} S'$ admits a neighbourhood $U$ over which $e^{*}\mathcal L_{Y'}$ and $\mathcal L_Y$ become isomorphic after restriction to the preimage of $U$.
--
--   This is the uniqueness half of base change for framed polarised abelian schemes: the fibre product of a framed object along a ring homomorphism is determined up to framed isomorphism, the frame clause being obtained from the two cartesian squares and the cartesian square $\mathbb P^N_{S'} \to \mathbb P^N_S$ over $\operatorname{Spec}\varphi$ rather than by cancelling a non-monomorphism. It is used in the construction of covers by reframed objects adapted to theta data, where two descriptions of the same base change have to be identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isPullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isPullback_of_isPullback
    {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : FramedPolarisedAbelianScheme g N n S) (Y Y' : FramedPolarisedAbelianScheme g N n S')
    (h : FramedPolarisedAbelianScheme.IsPullback φ X Y) (h' : FramedPolarisedAbelianScheme.IsPullback φ X Y') :
    FramedPolarisedAbelianScheme.Iso Y Y' := by sorry
