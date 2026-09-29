-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen
-- name    : AlgebraicGeometry.Scheme.exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/0231b49a-20a1-5c8d-b734-a68ccaf0d466
-- title:
--   Open subfunctor criterion: a compatible family of opens comes from an open of E
-- statement:
--   Let $E$ be a scheme and suppose given, for every commutative ring $R$ in the ambient universe and every morphism $s \colon \operatorname{Spec} R \to E$, a subset $U(R,s)$ of the underlying space of $\operatorname{Spec} R$, subject to two hypotheses: each $U(R,s)$ is open, and for all rings $R, R'$, every ring homomorphism $\psi \colon R \to R'$ and every $s \colon \operatorname{Spec} R \to E$ one has $U(R', \operatorname{Spec}(\psi)\text{ followed by }s) = (\operatorname{Spec}\psi)^{-1}\bigl(U(R,s)\bigr)$ on underlying spaces. The conclusion asserts the existence of an open subset $V$ of $E$ such that, first, for every ring $R$ and every $s \colon \operatorname{Spec} R \to E$ the preimage of $V$ under the continuous map underlying $s$ equals $U(R,s)$, and second, for every such $R$ and $s$ the image of the underlying map of $s$ is contained in $V$ if and only if $U(R,s)$ is all of $\operatorname{Spec} R$. Both clauses are universally quantified over $R$ and $s$ inside the existential, so the single open $V$ works for all affine points simultaneously.
--
--   This is the open-subscheme form of the functor-of-points recognition criterion: a rule assigning to each affine point of $E$ an open subset of its source, compatible with ring maps, is cut out by a unique open subset of $E$, and the equivalent 'the point factors through $V$' form is the shape used by subfunctor arguments. It is used in the construction of the open-plus-closed decomposition recorded in [`AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_forall_exists_comp_eq_iff_of_ideal_of_isOpen`](thm.html#AlgebraicGeometry.Scheme.exists_isOpenImmersion_isClosedImmersion_forall_exists_comp_eq_iff_of_ideal_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_forall_range_subset_iff_eq_univ_of_forall_isOpen
    (E : Scheme.{u})
    (U : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Set ↥(Spec (CommRingCat.of R)))
    (hUopen : ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), IsOpen (U R s))
    (hU : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      U R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (Spec.map (CommRingCat.ofHom ψ)).base ⁻¹' (U R s)) :
    ∃ V : E.Opens,
      (∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E), s.base ⁻¹' (V : Set E) = U R s) ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        Set.range s.base ⊆ (V : Set E) ↔ U R s = Set.univ := by sorry
