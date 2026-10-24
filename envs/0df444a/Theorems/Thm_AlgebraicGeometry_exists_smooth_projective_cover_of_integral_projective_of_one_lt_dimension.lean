-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_integral_projective_of_one_lt_dimension
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_one_lt_dimension
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-23T15:50:17.544673+00:00
-- url     : https://prove2.me/theorems/eb4e13cf-a107-46d0-81ae-141a7f8a8cc5
-- title:
--   Smooth integral projective covers in dimension at least two
-- statement:
--   Let $K$ be an algebraically closed field and let $X$ be an integral proper $K$-scheme with a fixed closed immersion into a projective space. Suppose that the dimension of $X$ is greater than one. Then there exist an integral smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$f:Y\longrightarrow X.$$
--   An actual closed immersion $j:Y\hookrightarrow\mathbb P^m_K$ is required, with the structural-map identity over $K$.
--
--   This is the remaining higher-dimensional case of the regular-alteration consequence. It allows every characteristic and assumes no regularity or smoothness of $X$. Only the indicated dimension range is restricted; all geometric conclusions of the integral-projective cover problem are retained.
-- source:
--   A. J. de Jong, Smoothness, semi-stability and alterations, Publ. Math. IHES 83 (1996), Theorem 4.1, Remark 4.2 and the dimension induction in Section 4.3, p.66; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This is the proper projective specialization over an algebraically closed (hence perfect) field, omitting generic finiteness and boundary-divisor data. The dimension-zero case is elementary; the curve case follows by normalization and projectivity of proper curves. See also Stacks Project, Section 53.2, Lemma 53.2.8, https://stacks.math.columbia.edu/tag/0BXX, and Section 33.27, https://stacks.math.columbia.edu/tag/0BXQ .

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
open TopologicalSpace

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective_of_one_lt_dimension
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by sorry
