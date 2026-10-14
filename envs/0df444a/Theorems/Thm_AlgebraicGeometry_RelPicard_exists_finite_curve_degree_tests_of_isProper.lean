-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_curve_degree_tests_of_isProper
-- name    : AlgebraicGeometry.RelPicard.exists_finite_curve_degree_tests_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-13T15:45:25.354749+00:00
-- url     : https://prove2.me/theorems/e0099dd2-8aaa-48ef-a623-408970abed56
-- title:
--   Finitely many smooth-curve degrees detect numerical triviality
-- statement:
--   Let $X$ be a proper scheme over an algebraically closed field $K$. A curve test consists of a smooth proper integral $K$-curve $C$, a $K$-morphism $f:C\to X$, and two affine open charts covering $C$. For an invertible sheaf $L$ on $X$, put
--
--   $$d_{C,f}(L)=\chi(C,f^*L)-\chi(C,\mathcal O_C).$$
--
--   There is a finite set $S$ of such tests, depending only on $X$, such that every invertible sheaf satisfies
--
--   $$\bigl(d_{C,f}(L)=0\text{ for every }(C,f)\in S\bigr)
--   \ \Longrightarrow\ d_{C,f}(L)=0\text{ for every curve test }(C,f).$$
--
--   The degrees are the actual two-chart Cech Euler characteristics. The finite test set is chosen before the line bundle. It may be empty. No smoothness, reducedness, integrality, projectivity, or connectedness of $X$ is assumed.
--
--   This is a finite-detection consequence of the numerical-rank argument in the cited source, expressed with normalized smooth curves mapping to $X$. It asserts no finite generation modulo algebraic equivalence.
-- source:
--   Cheng, Ji, Larson and Olander, Theorem of the Base (1 July 2021), Lemma 5.4 and Proposition 5.5, pp. 15-16; Lemma 6.1, p. 16; and the numerical-rank reduction in Theorem 7.4, pp. 18-19. https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf. Finite-dimensionality of the numerical pairing gives a finite detecting subfamily; normalize integral curves and use degree compatibility under proper pullback. This is a derived finite-detection formulation, not a literal source statement. Compare SGA 6, Expose XIII, Proposition 5.2, pp. 650-651.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.RelPicard.exists_finite_curve_degree_tests_of_isProper    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ s : Finset (CurveDegreeTests.Probe π),
      ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
        (∀ t ∈ s, t.degree M = 0) → CurveDegreeTests.NumericallyTrivial π M := by
  sorry
