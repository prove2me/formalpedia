-- Prove2me | Theorems.Thm_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
-- name    : AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/46fed16c-d0ab-578c-ac0b-9bbb4a4aac7e
-- title:
--   Universal closedness tested on finite affine spaces over the base
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $f : X \to \operatorname{Spec} R$ a morphism of schemes that is quasi-compact. Assume that for every finite index type $\iota$ (in the same universe) the second projection of the fibre product of $f$ with the morphism $\operatorname{Spec} R[x_i : i \in \iota] \to \operatorname{Spec} R$ induced by the structure map $R \to \operatorname{MvPolynomial}\ \iota\ R$, that is the base change
--   $$X \times_{\operatorname{Spec} R} \operatorname{Spec} R[x_i : i \in \iota] \longrightarrow \operatorname{Spec} R[x_i : i \in \iota],$$
--   has underlying continuous map on topological spaces a closed map. The conclusion is that $f$ is universally closed, i.e. every base change of $f$ along an arbitrary morphism of schemes is a closed map. Thus the hypothesis is only imposed for base changes to affine spaces on finitely many variables over the affine base, while the conclusion quantifies over all base changes.
--
--   This is the standard criterion for universal closedness of a quasi-compact morphism over an affine base: it suffices to test closedness after base change to the affine spaces $\mathbb{A}^n_R$ (Stacks 05JX, EGA II 5.6). Its proof passes from finitely many to arbitrarily many variables through [`AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra`](thm.html#AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra), and it is used in the valuative criterion for universal closedness in the form [`AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift`](thm.html#AlgebraicGeometry.universallyClosed_of_forall_isDiscreteValuationRing_finite_residueField_hasLift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (H : ∀ (ι : Type u) [Finite ι], IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R))))).base) :
    UniversallyClosed f := by sorry
