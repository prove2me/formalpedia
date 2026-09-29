-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7537bf71-2ce2-5c07-9aa2-62b077cf17a1
-- title:
--   δ-theta type, étale-locally, is stable under base change
-- statement:
--   Fix natural numbers $g, N, n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ nonzero, commutative rings $S, S'$ and a ring homomorphism $\varphi : S \to S'$. Let $u$ be a polarised abelian scheme of relative dimension $g$, geometric fibre $H^0$-rank $N+1$ and level $n$ over $S$ (an $S$-scheme $f : A \to \operatorname{Spec} S$ with a commutative relative group law, the property bundle, fibres of Krull dimension $g$, $2g$ marked $n$-torsion sections generating the $n$-torsion of every geometrically algebraically closed fibre freely, and an invertible module $\mathrm{pol}$ which is very ample by sections with geometric fibre rank $N+1$), and let $u'$ be such an object over $S'$. Assume `PolarisedAbelianScheme.IsPullback φ u u'`: there is a morphism $g_A : u'.A \to u.A$ making the square with $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ cartesian, compatible with the group laws on $T$-points, carrying each marked section $u'.P_i$ to $u.P_i$ over $\operatorname{Spec}\varphi$, and with $g_A^*(u.\mathrm{pol}) \cong u'.\mathrm{pol}$. Assume further that $u$ has $\delta$-theta type étale-locally over $S$: for every commutative $S$-algebra $R$ and every $\zeta \in R$ with $\zeta^{N+1} = 1$ and $1 - \zeta^j$ a unit for $0 < j < N+1$, there is a faithfully flat étale $R$-algebra $R'$, a framed polarised abelian scheme $X'$ over $R'$ (a polarised abelian scheme together with a $\mathrm{Proj}$ presentation of its polarisation by $N+1$ sections forming a section basis and inducing a closed immersion) and a bijection $e : \mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$ such that the underlying polarised abelian scheme of $X'$ is the base change of $u$ along $R \to R'$ composed with $S \to R$, and the frame of $X'$ is theta-adapted to $\delta$ and $e$ (its sections are those of a Schrödinger frame). The conclusion is that $u'$ has $\delta$-theta type étale-locally over $S'$.
--
--   This is the base-change stability of the property 'is, after a faithfully flat étale cover, the pullback of a framed polarised abelian scheme carrying a theta-adapted (Schrödinger) frame', the property used to cut out the moduli problem for polarised abelian schemes with theta structures of type $\delta$. It is invoked when the functor of polarised abelian schemes of $\delta$-theta type is shown to be representable by a quasi-projective fine moduli scheme, and in the transfer of the property along isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaTypeLocally_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaTypeLocally_of_isPullback
    {g N n : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)]
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S')
    (h : PolarisedAbelianScheme.IsPullback φ u u') (hu : PolarisedAbelianScheme.ThetaTypeLocally δ S u) :
    PolarisedAbelianScheme.ThetaTypeLocally δ S' u' := by sorry
