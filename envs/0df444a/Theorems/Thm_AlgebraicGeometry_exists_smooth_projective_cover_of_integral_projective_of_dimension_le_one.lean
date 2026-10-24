-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_integral_projective_of_dimension_le_one
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T15:50:03.758582+00:00
-- url     : https://prove2.me/theorems/0f1c9f8c-458b-4498-86e9-9ea1946208b1
-- title:
--   Smooth projective covers in dimension at most one
-- statement:
--   Let $K$ be an algebraically closed field and let $X$ be an integral proper $K$-scheme, equipped with a closed immersion into a projective space. Suppose that the dimension of $X$ is at most one. Then there exist an integral smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$f:Y\longrightarrow X.$$
--   Projectivity of $Y$ is exhibited by an actual closed immersion $j:Y\hookrightarrow\mathbb P^m_K$ compatible with the structural maps to $\operatorname{Spec}K$.
--
--   The statement includes the zero-dimensional case and makes no restriction on the characteristic. It provides the low-dimensional case of the regular-alteration construction and a smooth projective cover for a possibly singular integral projective curve. No smoothness or normality is assumed for $X$.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publ. Math. IHES 83 (1996), Theorem 4.1, Remark 4.2 and the dimension induction in Section 4.3, p.66; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This is the proper projective specialization over an algebraically closed (hence perfect) field, omitting generic finiteness and boundary-divisor data. The dimension-zero case is elementary; the curve case follows by normalization and projectivity of proper curves. See also Stacks Project, Section 53.2, Lemma 53.2.8, https://stacks.math.columbia.edu/tag/0BXX, and Section 33.27, https://stacks.math.columbia.edu/tag/0BXQ .

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
open TopologicalSpace

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_dimension_le_one
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by sorry
