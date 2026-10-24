-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_linear_realization_of_curve_degrees
-- name    : AlgebraicGeometry.RelPicard.exists_finite_linear_realization_of_curve_degrees
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-23T14:20:59.123984+00:00
-- url     : https://prove2.me/theorems/af6f8cbc-f793-48f3-b681-f46648587657
-- title:
--   Finite cohomological realization of smooth-curve line-bundle degrees
-- statement:
--   Let $K$ be an algebraically closed field and let $X$ be a smooth proper $K$-scheme with a fixed closed immersion into a projective space. Let $\mathcal P_X$ be the collection of smooth proper integral curves $C$ mapping to $X$, each supplied with two affine charts. For an invertible sheaf $M$ and a probe $t=(C,a)$, define its degree by the actual Cech Euler characteristics
--   $$d_M(t)=\chi(C,a^*M)-\chi(C,\mathcal O_C)\in\mathbb Z.$$
--   There exist a field $F$ of characteristic zero, a finite integer $r\geq0$, vectors $v_t\in F^r$ for all probes, and $F$-linear functionals $L_M:F^r\to F$ for all invertible sheaves such that
--   $$\iota(d_M(t))=L_M(v_t)\quad\text{for every }M,t,$$
--   where $\iota:\mathbb Q\hookrightarrow F$ is the canonical embedding and integers are viewed in $\mathbb Q$.
--
--   This is the finite linear realization supplied by cycle classes and their pairing in a Weil cohomology theory, with the comparison to the displayed concrete Cech degrees included. The assertion allows empty and disconnected schemes, components of different dimensions, and $r=0$. It assumes no finite generation or finite rational rank of a Neron-Severi group.
--
--   **Formalization Note.** Only the resulting finite vector space and its degree identity are asserted; no cohomology axioms or geometric realization are added to the definitions.
-- source:
--   Derived consequence of Cheng, Ji, Larson and Olander, Theorem of the Base (1 July 2021), Lemma 5.2, p.14, Lemma 5.4 and Proposition 5.5, pp.15-16; https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf . Use the cycle-class pairing with the finite-dimensional span of curve classes in a characteristic-zero Weil cohomology theory, and take the finite direct sum over the components. The curve-normalization, finite-map degree and Cech Euler comparisons needed for the displayed degree identity remain part of this input. This is an auxiliary finite-coordinate realization, not a literal transcription of Proposition 5.5 and not an assumption of the numerical-rank conclusion.

import Mathlib
import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.RelPicard.exists_finite_linear_realization_of_curve_degrees
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] [Smooth π]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (F : Type u) (_ : Field F) (_ : CharZero F) (r : ℕ)
      (v : CurveDegreeTests.Probe π → Fin r → F)
      (L : {M : X.Modules // Scheme.Modules.IsInvertible M} →
        Module.Dual F (Fin r → F)),
      ∀ M t, algebraMap ℚ F (t.degree M.val : ℚ) = L M (v t) := by sorry
