-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_of_isPullback_comp
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.of_isPullback_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/72fb5c00-9daf-561e-834d-87f2aeb70ac8
-- title:
--   Cancellation of base change for polarised abelian schemes
-- statement:
--   Fix natural numbers $g,d,n$, commutative rings $S,S',S''$, ring homomorphisms $\varphi : S \to S'$ and $\psi : S' \to S''$, and objects $u$, $v$, $w$ of `PolarisedAbelianScheme g d n` over $S$, $S'$, $S''$ respectively, each consisting of a scheme with a structure morphism to the spectrum of the base ring, a commutative relative group law, the smoothness/properness/connected-fibres bundle, fibres of topological Krull dimension $g$, a family $P_i$ ($i < 2g$) of $n$-torsion sections whose $\mathbb{Z}/n$-combinations are independent and exhaust the $n$-torsion on geometric fibres, and an invertible module $\mathrm{pol}$ which is very ample in the sense of admitting a projective presentation that is a closed immersion and has geometric fibrewise $H^0$-rank $d$. Here `PolarisedAbelianScheme.IsPullback` of a ring map applied to a pair of such objects asserts the existence of a morphism on total spaces making the square with the two structure morphisms and the induced map of spectra cartesian, compatible with multiplication of relative points, sending the marked sections of the target object to the base changes of those of the source, and identifying the pullback of the polarising module with the polarising module of the object over the larger ring. Assuming $w$ is such a pullback of $u$ along $\psi \circ \varphi$, and $v$ is such a pullback of $u$ along $\varphi$, the conclusion is that $w$ is such a pullback of $v$ along $\psi$.
--
--   This is the cancellation half of the pasting law for cartesian squares, upgraded so that it also transports the group law, the level-$n$ structure and the polarisation. It is used when tautological polarised abelian schemes over nested opens of a moduli space must be exhibited as successive base changes of one another, and is cited in the construction of fine moduli data and in the local theta-type statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_of_isPullback_comp.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.of_isPullback_comp
    {g d n : ℕ} {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S') (w : PolarisedAbelianScheme g d n S'')
    (h : PolarisedAbelianScheme.IsPullback (ψ.comp φ) u w) (h₁ : PolarisedAbelianScheme.IsPullback φ u v) :
    PolarisedAbelianScheme.IsPullback ψ v w := by sorry
