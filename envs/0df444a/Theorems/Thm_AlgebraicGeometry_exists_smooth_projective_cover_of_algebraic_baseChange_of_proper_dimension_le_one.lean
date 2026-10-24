-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T22:44:24.938976+00:00
-- url     : https://prove2.me/theorems/98944e77-2d0a-41a3-bad1-20bd6211e2e8
-- title:
--   Smooth projective covers of proper curves after algebraic base change
-- statement:
--   Let $K$ be a field and let $L/K$ be an algebraic extension with $L$ algebraically closed. Let $X$ be any proper $K$-scheme of dimension at most one. For the actual base-changed scheme
--   $$X_L=X\times_{\operatorname{Spec}K}\operatorname{Spec}L,$$
--   there exist a smooth projective $L$-scheme $Y$ of dimension at most one and a proper surjective $L$-morphism
--   $$f:Y\longrightarrow X_L.$$
--   Projectivity is exhibited by a closed immersion of $Y$ into a finite-dimensional projective space over $L$, compatible with the displayed structure map.
--
--   Neither $X$ nor $X_L$ is required to be reduced, irreducible, connected or nonempty. The extension $L/K$ need not be finite. Taking $L$ to be an algebraic closure gives a smooth projective cover of the geometric curve, even if the original curve over its imperfect ground field is not smooth.
--
--   **Formalization Note.** The assertion concerns the displayed fibre product and its actual structure morphism to $\operatorname{Spec}L$. It does not descend the cover to a finite intermediate extension, identify the cover with a canonical normalization, assert that $Y$ is integral, or produce a semistable family.
-- source:
--   Derived consequence of componentwise normalization of proper curves and projectivity of proper regular curves: Stacks Project, Lemma 53.2.9(1) and its normalization argument, https://stacks.math.columbia.edu/tag/0BY4 , and the componentwise treatment of geometric curves in Section 53.18, https://stacks.math.columbia.edu/tag/0CE0 . The algebraic base-change dimension bound uses stability of integral morphisms under base change and their dimension inequality, Lemmas 29.45.6 and 29.45.9, https://stacks.math.columbia.edu/tag/01WG . This formulation includes reducible, nonreduced and empty proper schemes via the finite disjoint union of smooth projective covers of their reduced irreducible components. It is preparatory geometric-generic-curve infrastructure for the alteration branch of the Philippon mission, and is not the finite purely inseparable descent assertion of Lemma 53.2.9(2).

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_algebraic_baseChange_of_proper_dimension_le_one
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed L] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsProper π]
    (hdim : topologicalKrullDim X ≤ 1) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
    ∃ (Y : Scheme.{u}) (f : Y ⟶ pullback π b),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ pullback.snd π b) ∧
      topologicalKrullDim Y ≤ 1 ∧
      ∃ (n : ℕ) (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) L)),
        IsClosedImmersion i ∧ i ≫ ProjSpace.π L n = f ≫ pullback.snd π b := by sorry
