-- Prove2me | Theorems.Thm_AlgebraicGeometry_forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective
-- name    : AlgebraicGeometry.forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/f5868a98-6580-559e-ba74-6ef9fd63431e
-- title:
--   Affine neighbourhoods of finite sets descend along surjective closed immersions
-- statement:
--   Let $Z$ and $X$ be schemes and let $f : Z \to X$ be a morphism that is a closed immersion and surjective. Suppose two hypotheses: first, that affineness of opens transfers from $Z$ to $X$ along $f$, in the sense that for every open subscheme $U$ of $X$, if the scheme-theoretic preimage $f^{-1}(U)$ is an affine open of $Z$ then $U$ is an affine open of $X$; second, that $Z$ has the property that every finite subset $S \subseteq Z$ of its underlying space is contained in some affine open $U$ of $Z$. The conclusion is that $X$ has the same property: for every subset $S$ of the underlying space of $X$ which is finite, there exists an open $U \subseteq X$ which is an affine open and satisfies $S \subseteq U$.
--
--   A surjective closed immersion is a homeomorphism on underlying spaces, so the statement says that the property ‘every finite set of points lies in an affine open’ passes from a closed subscheme to the ambient scheme once affineness of opens is known to lift; the affineness-transfer assumption is the genuinely scheme-theoretic input and is assumed here. It is used in the construction of Mumford-style formal glueing data in the Čerednik–Drinfel'd part of the development, to produce affine neighbourhoods on a thickening from affine neighbourhoods on its closed fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.forall_finite_exists_isAffineOpen_of_isClosedImmersion_of_surjective
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f] [Surjective f]
    (hAff : ∀ U : X.Opens, IsAffineOpen (f ⁻¹ᵁ U) → IsAffineOpen U)
    (hZ : ∀ S : Set Z, S.Finite → ∃ U : Z.Opens, IsAffineOpen U ∧ S ⊆ (U : Set Z)) :
    ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X) := by sorry
