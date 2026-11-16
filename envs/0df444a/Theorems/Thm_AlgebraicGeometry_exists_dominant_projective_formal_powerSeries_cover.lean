-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_dominant_projective_formal_powerSeries_cover
-- name    : AlgebraicGeometry.exists_dominant_projective_formal_powerSeries_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-16T00:23:16.325098+00:00
-- url     : https://prove2.me/theorems/6cc9655c-7d99-4651-97d3-2a6b9b9fc87c
-- title:
--   Dominant projective covers with formal power-series models
-- statement:
--   Let $K$ be an algebraically closed field and let $X$ be a normal integral projective $K$-scheme of dimension greater than one, with its given projective embedding and structure morphism $\pi$. There exist an integral $K$-scheme $Y$, a dominant morphism $a:Y\to X$, and a closed projective embedding of $Y$ whose structure morphism is exactly $\pi\circ a$, such that
--   $$\dim Y\leq\dim X.$$
--   For every closed point $y\in Y$, there is a finite number $r_y$ of variables and an isomorphism of rings
--   $$\widehat{\mathcal O}_{Y,y}\cong K[[t_1,\ldots,t_{r_y}]].$$
--   Here the completion is taken at the maximal ideal of the actual scheme stalk. The field characteristic is unrestricted, and all schemes retain the original universe.
--
--   This is the geometric construction input in a formal-local formulation of the projective case of de Jong's alteration theorem. Constructing the cover and its simultaneous formal models remains the open task. A separate checked reduction proves that these data imply regularity at every point, properness, surjectivity, and finiteness over a nonempty open of $X$. The statement does not assume any of those four conclusions, and it does not ask to algebraize individual formal isomorphisms into an atlas.
-- source:
--   Formal-local construction formulation of the normal projective algebraically closed case of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Theorem 4.1, Remark 4.2 and Sections 4.3–4.5 and 4.10, pp. 66–68; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This is a reformulation of the construction output, not a verbatim numbered statement: the smooth projective cover produced there has formal power-series stalks at its closed points over an algebraically closed field. The dimension bound retains generic finiteness. The associated reduction separately proves completion regularity and the passage from closed points to all points, and derives the required finite open locus using the dimension formula and Stacks Project Lemma 37.44.2, Tag 02UP, https://stacks.math.columbia.edu/tag/02UP .

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
open TopologicalSpace

theorem AlgebraicGeometry.exists_dominant_projective_formal_powerSeries_cover
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsDominant a ∧ topologicalKrullDim Y ≤ topologicalKrullDim X ∧
      (∀ y : Y, IsClosed ({y} : Set Y) →
        ∃ r : ℕ, Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y) ≃+* MvPowerSeries (Fin r) K)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by sorry
