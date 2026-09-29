-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents
-- name    : AlgebraicGeometry.exists_isFinite_to_proj_of_completeOrthogonalIdempotents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/4400e756-b588-58e6-b6e5-d34b8cd84a14
-- title:
--   Finite morphisms to a Proj glue over an idempotent decomposition
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme and let $f\colon X \to \operatorname{Spec} R$ be a morphism of schemes. Let $m$ be a natural number and let $e\colon \mathrm{Fin}\,m \to R$ be a family of complete orthogonal idempotents, i.e. each $e_i$ is idempotent, $e_ie_j = 0$ for $i \neq j$, and $\sum_i e_i = 1$. Suppose that for every index $i$ there exist a commutative ring $A$, a type $\sigma$ of additive subgroups of $A$ (given by `SetLike` and `AddSubgroupClass` instances), a family $\mathcal{A}\colon \mathbb{N} \to \sigma$ making $A$ into an $\mathbb{N}$-graded ring, and a morphism $\iota$ from the fibre product of $f$ with $\operatorname{Spec}$ of the localisation map $R \to R[e_i^{-1}]$ (the localisation away from $e_i$) to $\operatorname{Proj} \mathcal{A}$ which is a finite morphism of schemes. Then the same data exist for $X$ itself: there are a commutative ring $A$, a type $\sigma$ of additive subgroups of $A$, an $\mathbb{N}$-grading $\mathcal{A}$ on $A$, and a finite morphism $\iota\colon X \to \operatorname{Proj} \mathcal{A}$. All rings, types and schemes live in a single universe $u$.
--
--   The statement records that the property of admitting a finite morphism to the $\operatorname{Proj}$ of an $\mathbb{N}$-graded ring is local with respect to a decomposition of the base ring into complete orthogonal idempotents, the underlying geometric facts being that $\operatorname{Proj}$ of a finite product of graded rings is the disjoint union of the $\operatorname{Proj}$'s of the factors and that finiteness is local on the target. It serves to reduce assertions of the form "$X$ is finite over a projective scheme" to the case of a base with no nontrivial idempotents, and is used in the construction of finite morphisms to projective schemes in the relative Picard scheme material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isFinite_to_proj_of_completeOrthogonalIdempotents.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_isFinite_to_proj_of_completeOrthogonalIdempotents
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {m : ℕ} (e : Fin m → R)
    (he : CompleteOrthogonalIdempotents e)
    (hfin : ∀ i : Fin m, ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜)
      (ι : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e i))))) ⟶ Proj 𝒜),
      IsFinite ι) :
    ∃ (A σ : Type u) (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ)
      (_ : GradedRing 𝒜) (ι : X ⟶ Proj 𝒜), IsFinite ι := by sorry
