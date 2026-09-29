-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
-- name    : AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/c26d81b6-d4f2-5711-a831-c711dee1e68b
-- title:
--   Chow's lemma, envelope form, for integral schemes
-- statement:
--   Let $A$ be a commutative Noetherian ring and let $X$ be a scheme which is integral (reduced and irreducible), and let $f \colon X \to \operatorname{Spec} A$ be a morphism of schemes which is separated, locally of finite type and quasi-compact, all three in the sense of the corresponding Mathlib morphism properties; all schemes live in a single universe. The assertion is that there exist schemes $X'$ and $P$ together with morphisms $\pi \colon X' \to X$, $j \colon X' \to P$ and $q \colon P \to \operatorname{Spec} A$ such that $\pi$ is proper and surjective, $j$ is an open immersion, $q$ is proper, and the square commutes in the sense that $j$ followed by $q$ equals $\pi$ followed by $f$, i.e. $q \circ j = f \circ \pi$. Note that $P$ is only required to be proper over $A$; no projectivity or quasi-projectivity of $P$, $X'$ or of the morphisms $\pi$, $q$ is asserted, and no compatibility of $j$ with any other structure beyond the stated commutativity is claimed.
--
--   This is the integral case of Chow's lemma in a weak "envelope" form, in which the compactification of $X'$ is only required to be proper over the base rather than projective. It is the inductive input to [`AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated`](thm.html#AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated), which removes the integrality hypothesis by Noetherian induction on the irreducible components; the proof produces the ambient proper scheme out of projective space over $A$, using the presentation of the standard affine charts of projective space by homogeneous localisation recorded in [`AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq`](thm.html#AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f := by sorry
