-- Prove2me | Theorems.Thm_FiniteFields_LinearAlgebra_logDerivative_fredholmDeterminant
-- name    : FiniteFields.LinearAlgebra.logDerivative_fredholmDeterminant
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-20T01:58:10.66874+00:00
-- url     : https://prove2.me/theorems/392b8087-d3d4-4ebb-accb-19c63a0d7e0c
-- title:
--   Jacobi's formula for the logarithmic derivative of $\det(1 - Xu)$
-- statement:
--   Let $R$ be a commutative ring, $M$ a free $R$-module of finite rank $r$, and $u \in \operatorname{End}_R(M)$. The **Fredholm determinant** of $u$ is the polynomial
--   $$D_u(X) = \det(1 - X u) = X^{r} \chi_u(X^{-1}) \in R[X],$$
--   defined without a basis as the reverse of the characteristic polynomial $\chi_u$. Its constant term is $1$, so $D_u$ is invertible in $R[[X]]$, and its **negative logarithmic derivative** is the power series
--   $$\Lambda_u(X) = -D_u'(X)\, D_u(X)^{-1} \in R[[X]].$$
--
--   **Statement.** Let $b = (b_i)_{i \in \iota}$ be a basis of $M$ indexed by a finite type $\iota$, and let $A \in M_\iota(R)$ be the matrix of $u$ in $b$. Then
--   $$-\frac{D_u'(X)}{D_u(X)} \;=\; \frac{\operatorname{tr}\!\big(\operatorname{adj}(1 - XA)\, A\big)}{D_u(X)} \qquad \text{in } R[[X]],$$
--   where $1 - XA \in M_\iota(R[X])$ and $\operatorname{adj}$ is the classical adjugate matrix.
--
--   This is the integral, finite-dimensional form of Jacobi's formula: the numerator of the logarithmic derivative of $\det(1 - Xu)$ is the trace of the adjugate resolvent. It is valid over any commutative ring, with no invertibility assumption on $1 - XA$ as a polynomial matrix, and underlies the identification of traces of powers of an operator with the coefficients of the logarithmic derivative of its Fredholm determinant.
--
--   **Formalization Note.** $D_u(X)^{-1}$ is `PowerSeries.invOfUnit D_u 1`, the power-series inverse of a series with constant coefficient $1$, which exists over any commutative ring (over a field it is the ordinary inverse). The entries of $A$ are embedded in $R[X]$ as constant polynomials, and the polynomials are viewed in $R[[X]]$ by the canonical coercion. $D_u$ is `fredholmDeterminant u` and $\Lambda_u$ is `fredholmLogDerivative u`.
-- source:
--   B. Dwork, *On the rationality of the zeta function of an algebraic variety*, Amer. J. Math. 82 (1960), 631–648, §3, (16)–(21) (zeta function expressed through traces and Fredholm determinants). Auxiliary finite-dimensional lemma (Jacobi's formula) in the formalization of §3 of Dwork 1960; it is not stated in the paper. Lean: ported from the `finite_fields` project (commit e8b5bf14), file `WeilConjectures/LinearAlgebra/Fredholm.lean`, declaration `WeilConjectures.LinearAlgebra.logDerivative_fredholmDeterminant`

import Mathlib
import Definitions.Def_FiniteFields_Dwork_TraceFormula

open Module Polynomial PowerSeries
open FiniteFields.LinearAlgebra
universe u v w
variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem FiniteFields.LinearAlgebra.logDerivative_fredholmDeterminant (u : Module.End R M)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    fredholmLogDerivative u =
      ((Matrix.trace
          ((1 - (X : R[X]) • (LinearMap.toMatrix b b u).map Polynomial.C).adjugate *
            (LinearMap.toMatrix b b u).map Polynomial.C) : R[X]) : R⟦X⟧) *
        PowerSeries.invOfUnit (fredholmDeterminant u : R⟦X⟧) 1 := by sorry
