-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_bounded_numerically_trivial_family_of_isProper
-- name    : AlgebraicGeometry.RelPicard.exists_bounded_numerically_trivial_family_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-13T15:44:29.883164+00:00
-- url     : https://prove2.me/theorems/8ed980e2-b128-4eb4-9d63-1f797c9a2833
-- title:
--   A finite-type family containing all numerically trivial line bundles
-- statement:
--   Let $X$ be a proper scheme over an algebraically closed field $K$. Call an invertible sheaf $N$ numerically trivial when
--
--   $$\chi(C,f^*N)-\chi(C,\mathcal O_C)=0$$
--
--   for every smooth proper integral $K$-curve $C$ and every $K$-morphism $f:C\to X$. Euler characteristics use any two affine charts covering the curve.
--
--   There exist a finite-type $K$-scheme $T$ and an invertible sheaf $M$ on $X\times_K T$ such that
--
--   $$\text{for every numerically trivial }N,\quad
--   \text{there is }t\in T(K)\text{ with }M_t\simeq N.$$
--
--   Neither $T$ nor $X$ is required to be smooth, reduced, integral, or connected. The parameter family is chosen once for all numerically trivial line bundles. No assertion is made that every fibre of $M$ is numerically trivial.
--
--   This is the bounded-family formulation of the finite-type torsion part of the Picard scheme, including its passage to a finite-type cover carrying an actual family. It is a consequence of the source results cited below, not their literal transcription.
-- source:
--   Cheng, Ji, Larson and Olander, Theorem of the Base (1 July 2021), Proposition 1.3 and Lemma 1.6, p. 4; Lemma 4.2, Proposition 4.3 and Theorem 4.4, pp. 13-14. https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf. For general proper X use the finite-type Picard torsion scheme from Theorem 4.4, its local universal invertible sheaf in the fppf topology, and a finite subcover. Over algebraically closed K every nonempty finite-type fibre has a rational point. Normalization of integral curves identifies the displayed degree tests with numerical triviality. This states the resulting bounded-family consequence explicitly, including the cover carrying the family.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
universe u

theorem AlgebraicGeometry.RelPicard.exists_bounded_numerically_trivial_family_of_isProper    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (T : Scheme.{u}) (h : T ⟶ Spec (.of K))
      (_ : LocallyOfFiniteType h) (_ : QuasiCompact h)
      (M : (pullback π h).Modules) (_ : Scheme.Modules.IsInvertible M),
      ∀ N : X.Modules, Scheme.Modules.IsInvertible N →
        CurveDegreeTests.NumericallyTrivial π N →
          ∃ t : SchemeHomOver (𝟙 (Spec (.of K))) h,
            Nonempty (CurveDegreeTests.fibre h M t ≅ N) := by
  sorry
