-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/efd9f09a-986e-5fa8-b32f-7846d3aa05a6
-- title:
--   Transitivity of base change for polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $d$, $n$, commutative rings $S$, $S'$, $S''$, and ring homomorphisms $\varphi : S \to S'$ and $\psi : S' \to S''$, together with polarised abelian schemes $u$ over $S$, $v$ over $S'$ and $w$ over $S''$, each of the data type `PolarisedAbelianScheme g d n` (a scheme with a structure morphism to the spectrum of the base, a commutative relative group law, the property bundle of smoothness, properness, connected fibres and existence of a group law, fibres of topological Krull dimension $g$, a family of $2g$ sections killed by $n$ which freely generate $(\mathbb{Z}/n)^{2g}$ on geometric fibres, and an invertible module, very ample in the sense of admitting a closed-immersion projective presentation, with geometric fibre $H^0$ of rank $d$). Assume that $v$ is a base change of $u$ along $\varphi$ and that $w$ is a base change of $v$ along $\psi$, where `IsPullback` for a homomorphism means: there is a morphism of the total spaces making the square over $\operatorname{Spec}$ of the homomorphism cartesian, compatible with the relative group laws on $T$-points, carrying the $i$-th marked section of the source to the base change of the $i$-th marked section of the target, and such that the pullback of the polarising module is isomorphic to the polarising module. The conclusion is that $w$ is a base change of $u$ along $\psi \circ \varphi$ in the same sense.
--
--   This is the transitivity (composition) statement for the base-change relation between polarised abelian schemes with level-$n$ structure, the standard functoriality needed to treat such data as a functor on rings. It is used throughout the moduli-theoretic part of the development, for instance in the results on fine moduli and on comparison of polarised abelian schemes over different bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_trans.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.trans
    {g d n : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S') (w : PolarisedAbelianScheme g d n S'')
    (h₁ : PolarisedAbelianScheme.IsPullback φ u v) (h₂ : PolarisedAbelianScheme.IsPullback ψ v w) :
    PolarisedAbelianScheme.IsPullback (ψ.comp φ) u w := by sorry
