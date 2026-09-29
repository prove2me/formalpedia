-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
-- name    : AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3af217e5-6941-5971-b5d5-0f465a9af175
-- title:
--   Chow's lemma in envelope form over a Noetherian base
-- statement:
--   Let $A$ be a Noetherian commutative ring, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} A$ be a morphism that is separated, locally of finite type and quasi-compact (so of finite type). Then there exist schemes $X'$ and $P$ together with morphisms $\pi \colon X' \to X$, $j \colon X' \to P$ and $q \colon P \to \operatorname{Spec} A$ such that: $\pi$ is proper; $\pi$ is surjective; $j$ is an open immersion; $q$ is proper; and $j$ followed by $q$ equals $\pi$ followed by $f$, i.e. $q \circ j = f \circ \pi$. Thus $X$ is covered, by a proper surjective morphism from $X'$, in such a way that $X'$ is realised as an open subscheme of a scheme $P$ proper over $\operatorname{Spec} A$, compatibly with the structure morphisms to $\operatorname{Spec} A$. No irreducibility, reducedness or integrality assumption is placed on $X$; the asserted conclusion records only the existence of such a diagram, not the usual additional property that $\pi$ be an isomorphism over a dense open subset of $X$.
--
--   This is a weak (envelope) form of Chow's lemma: a separated finite-type scheme over a Noetherian ring admits a proper surjective cover by an open subscheme of a proper scheme. It is deduced from the corresponding statement for integral $X$, and is used in the study of properness of morphisms obtained by base change, in [`AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd`](thm.html#AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd) and [`AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete`](thm.html#AlgebraicGeometry.exists_opens_isClosed_isProper_of_isProper_pullback_snd_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f := by sorry
