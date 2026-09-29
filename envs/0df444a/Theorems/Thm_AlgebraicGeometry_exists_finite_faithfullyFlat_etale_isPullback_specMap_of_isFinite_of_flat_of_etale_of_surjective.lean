-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective
-- name    : AlgebraicGeometry.exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/882f5a84-731a-5cb0-887d-5cd08a62b855
-- title:
--   Affine points lift through finite flat étale surjective covers
-- statement:
--   Let $H$ and $M$ be schemes (in a fixed universe) and let $q : H \to M$ be a morphism which is finite, flat and étale, and whose map on underlying topological spaces $q.\mathrm{base}$ is surjective. Let $S$ be a commutative ring in the same universe and let $x : \operatorname{Spec} S \to M$ be any morphism of schemes. The assertion is that there exist a type $S'$ in that universe, a commutative ring structure on $S'$ and an $S$-algebra structure on it, such that $S'$ is finite as an $S$-module, faithfully flat as an $S$-module and étale as an $S$-algebra (that is, formally étale and of finite presentation), together with a morphism $y : \operatorname{Spec} S' \to H$ for which the square with top edge $y$, left edge $\operatorname{Spec}$ of the structure morphism $S \to S'$, bottom edge $x$ and right edge $q$ commutes and is cartesian. Thus the base change of $q$ along any affine point of $M$ is, up to isomorphism, the spectrum of a finite faithfully flat étale $S$-algebra.
--
--   This is the standard statement that a finite flat étale surjective cover becomes, after pullback along an affine morphism to the base, the spectrum of a finite faithfully flat étale algebra; it converts a geometric covering datum into ring-theoretic data. It is used in the study of polarised abelian schemes, in the argument that a point exists after passing to such a cover ([`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_eq_of_finite_free_transitive`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_eq_of_finite_free_transitive)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.exists_finite_faithfullyFlat_etale_isPullback_specMap_of_isFinite_of_flat_of_etale_of_surjective
    {H M : Scheme.{u}} (q : H ⟶ M) [IsFinite q] [Flat q] [Etale q] (hqsurj : Function.Surjective q.base)
    {S : Type u} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ M) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.Finite S S' ∧ Module.FaithfullyFlat S S' ∧ Algebra.Etale S S' ∧
      ∃ y : Spec (CommRingCat.of S') ⟶ H, IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S S'))) y x q := by sorry
