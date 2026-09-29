-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
-- name    : AlgebraicGeometry.exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/b33b752f-7ade-5ac2-87da-0a47c7c9b0a3
-- title:
--   Finite part of a quasi-finite scheme over a henselian local ring
-- statement:
--   Let $R$ be a henselian local ring and let $g \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is locally of finite type, locally quasi-finite, separated and quasi-compact. Then there exist schemes $X^{\mathrm f}$ and $X'$ together with morphisms $i \colon X^{\mathrm f} \to X$ and $j \colon X' \to X$, both open immersions, such that: the composite $i$ followed by $g$, namely $g \circ i \colon X^{\mathrm f} \to \operatorname{Spec} R$, is a finite morphism; the set-theoretic images of $i$ and $j$ cover the underlying space of $X$, their union being all of $X$; these two images are disjoint (so $X$ is the disjoint union of two open, hence also closed, subschemes); and the closed point of $\operatorname{Spec} R$, i.e. the maximal ideal of the local ring $R$, does not lie in the image of $j$ followed by $g$. The last condition says that $X'$ has empty special fibre, so that $X^{\mathrm f}$ contains the whole fibre of $g$ over the closed point.
--
--   This is the existence of the finite part of a separated, quasi-compact, quasi-finite scheme over a henselian local ring (EGA IV 18.5.11(c)). It is obtained by gluing the affine statement that over a henselian local ring a quasi-finite finite-type algebra contains an idempotent cutting out a module-finite quotient and lying outside every prime over the maximal ideal, and it is used for the counting results comparing the number of sections of $g$ with the dimension of the special fibre, and for the variant of the decomposition in which the second piece is described by an empty pullback along the closed point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] :
    ∃ (Xf X' : Scheme.{u}) (i : Xf ⟶ X) (j : X' ⟶ X) (_ : IsOpenImmersion i)
      (_ : IsOpenImmersion j),
      IsFinite (i ≫ g) ∧
      Set.range i ∪ Set.range j = Set.univ ∧
      Disjoint (Set.range i) (Set.range j) ∧
      IsLocalRing.closedPoint R ∉ Set.range (j ≫ g) := by sorry
