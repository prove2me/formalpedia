-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.hasPrincipalRoot_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/833b43a3-fd70-594c-8972-8cd6e9ec4a23
-- title:
--   Base change preserves the existence of a principal root
-- statement:
--   Fix natural numbers $g$, $d$, $n$, commutative rings $S$, $S'$ and a ring homomorphism $\varphi : S \to S'$, together with polarised abelian schemes $u$ over $S$ and $u'$ over $S'$ of type $(g,d,n)$ (each consisting of a scheme $A$ over $\operatorname{Spec} S$ with a commutative relative group law, the property bundle of an abelian scheme, all fibres of Krull dimension $g$, a family of $2g$ sections killed by $n$ that is independent and spans the $n$-torsion on every algebraically closed geometric fibre, and an invertible module `pol` which embeds $A$ as a closed subscheme of a projective space by sections and has geometric fibre $H^0$-rank $d$). Assume `PolarisedAbelianScheme.IsPullback φ u u'`, that is, there is a morphism $g_A : u'.A \to u.A$ making the square formed by $g_A$, $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ a pullback square, such that $g_A$ is a homomorphism on $T$-points for the two group laws, carries each marked section $u'.P\,i$ to the base change of $u.P\,i$, and pulls $u.\mathrm{pol}$ back to a module isomorphic to $u'.\mathrm{pol}$. Assume further `HasPrincipalRoot u`: there is a faithfully flat $S$-algebra $S_2$ such that for every relative group law $L'$ on the projection $A \times_S S_2 \to \operatorname{Spec} S_2$ whose multiplication is compatible, on points, with $u.L$ along the other projection, there exist an invertible module $\mathcal L_0$ on $A \times_S S_2$ and natural numbers $a$, $b$ with $a + b \ge 1$ such that $\mathcal L_0$ has trivial kernel in the sense of `Polarisation.KernelTrivial` and the pullback of $u.\mathrm{pol}$ to $A \times_S S_2$ is, locally on the base, isomorphic to $\mathcal L_0^{\otimes a} \otimes ([-1]^{*}\mathcal L_0)^{\otimes b}$, where $[-1]$ is the inversion morphism `Polarisation.negMor` of $L'$. The conclusion is `HasPrincipalRoot u'`, the same statement for $u'$ over $S'$.
--
--   This is the base-change stability of the condition that a polarisation admit, faithfully flat locally on the base, a principal root $\mathcal L_0$ with trivial kernel, the polarisation being a product of $\mathcal L_0$ and its inverse-image under inversion. It feeds the corresponding base-change statement for polarised abelian schemes that are rooted and symmetric of a given type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.hasPrincipalRoot_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u u') (hu : PolarisedAbelianScheme.HasPrincipalRoot u) :
    PolarisedAbelianScheme.HasPrincipalRoot u' := by sorry
