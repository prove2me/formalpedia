-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_curve_degree_tests_of_smooth_projective
-- name    : AlgebraicGeometry.RelPicard.exists_finite_curve_degree_tests_of_smooth_projective
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-13T16:20:18.566122+00:00
-- url     : https://prove2.me/theorems/122116eb-a838-475b-a91c-87629ef43fd9
-- title:
--   Finite curve-degree detection on a smooth projective scheme
-- statement:
--   Let $X$ be a smooth proper scheme over an algebraically closed field $K$, equipped with a closed immersion into a finite-dimensional projective space over $K$. A curve test $t$ consists of a smooth proper integral curve $C$, a morphism $a:C\to X$ over $K$, and a two-affine-open cover of $C$. Define
--
--   $$d_t(L)=\chi(C,a^*L)-\chi(C,\mathcal O_C)$$
--
--   using the actual two-chart Cech section modules. There is a finite set $S$ of curve tests such that every invertible sheaf $L$ satisfies
--
--   $$\bigl(d_t(L)=0\text{ for all }t\in S\bigr)\Longrightarrow
--     \bigl(d_t(L)=0\text{ for all curve tests }t\bigr).$$
--
--   The finite set is chosen before $L$. It may be empty. Neither connectedness nor positive dimension is required of $X$.
--
--   This finite-detection consequence of the cited cohomological numerical-rank bound replaces an infinite family of degree conditions by finitely many tests. It is the smooth projective input for descent of numerical triviality to arbitrary proper schemes. The statement is a derived consequence, not a literal transcription of Proposition 5.5.
-- source:
--   Cheng, Ji, Larson and Olander, Theorem of the Base (1 July 2021), Lemma 5.4 and Proposition 5.5, pp. 15-16: https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf. Derived finite-detection consequence of the numerical pairing in codimension one, applied to the finitely many components. Normalize the integral curves used as tests and use Stacks Project, Lemmas 33.44.4 and 33.44.11 (https://stacks.math.columbia.edu/tag/0AYQ and https://stacks.math.columbia.edu/tag/0AYZ) for degrees under birational and nonconstant proper curve maps. This does not invoke the proper-scheme Neron-Severi finite-generation theorem being reduced.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.RelPicard.exists_finite_curve_degree_tests_of_smooth_projective
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] [Smooth π]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ s : Finset (CurveDegreeTests.Probe π),
      ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
        (∀ t ∈ s, t.degree M = 0) → CurveDegreeTests.NumericallyTrivial π M := by
  sorry
