-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
-- name    : AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/68bc5f3b-e5ff-5c45-93d2-6c6921e7a944
-- title:
--   Chow's lemma, birational form, over a Noetherian base
-- statement:
--   Let $A$ be a Noetherian commutative ring, let $X$ be an integral scheme, and let $f : X \to \operatorname{Spec} A$ be a morphism that is separated, locally of finite type and quasi-compact. Then there exist schemes $X'$ and $P$ and morphisms $\pi : X' \to X$, $j : X' \to P$ and $q : P \to \operatorname{Spec} A$ such that: $\pi$ is proper and surjective; $j$ is an open immersion; $q$ is proper; the square commutes, in the sense that $j$ followed by $q$ equals $\pi$ followed by $f$, i.e. $q \circ j = f \circ \pi$; both $X'$ and $P$ are integral schemes; and there is an open subscheme $U$ of $X$ with $U \neq \bot$ (that is, $U$ non-empty) such that the restriction $\pi \mid_{U}$ of $\pi$ over $U$, a morphism $\pi^{-1}(U) \to U$, is an isomorphism. All the schemes involved live in a single universe, as do the rings.
--
--   This is the birational form of Chow's lemma: a separated, quasi-compact, finite-type integral scheme over a Noetherian base admits a proper surjective modification that is an open subscheme of a proper $A$-scheme and is an isomorphism over a non-empty open set. It is used in the construction of a proper modification with integrally closed local rings, via [`AlgebraicGeometry.exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated`](thm.html#AlgebraicGeometry.exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f ∧
      IsIntegral X' ∧ IsIntegral P ∧ ∃ U : X.Opens, U ≠ ⊥ ∧ IsIso (π ∣_ U) := by sorry
