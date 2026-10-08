-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_lemma_8
-- name    : EmpiricalBernstein.SVP.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:28.139364+00:00
-- url     : https://prove2.me/theorems/44dc560c-dbc4-4d90-8dc8-62d0395c3e84
-- title:
--   Lemma 8 — $\mathbb E_X[(\mathbb E_Y(X-Y)^2)^2] \le \frac12\mathbb E(X-Y)^2$ for i.i.d. $X,Y$ in $[a,a+1]$
-- statement:
--   Let $X, Y$ be independent random variables with the same distribution $\nu$, taking values in an interval $[a, a+1]$ of length one. Then
--
--   $$
--   \mathbb E_X\Big[\big(\mathbb E_Y (X-Y)^2\big)^2\Big] \le \frac12\, \mathbb E (X-Y)^2 .
--   $$
--
--   Here $\mathbb E_Y(X-Y)^2 = \int (X-y)^2\,d\nu(y)$ is the conditional second moment given $X$, and the right side is $\frac12\iint (x-y)^2\,d\nu(x)\,d\nu(y) = \mathbb V X$.
--
--   This fourth-moment inequality is what makes the sample variance a self-bounding function, and so yields the concentration of the sample variance (Theorem 10).
--
--   **Formalization Note** $\nu$ is a probability measure on $\mathbb R$ with $\nu(\mathbb R\setminus[a,a+1]) = 0$; both sides are written as iterated integrals against $\nu$.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Lemma 8, p. 3

import Mathlib

open MeasureTheory

namespace EmpiricalBernstein.SVP

/-- Lemma 8 (arXiv:0907.3740v1, p. 3). `X, Y` i.i.d. with law `ν` concentrated on `[a, a + 1]`. -/
theorem lemma_8 (ν : Measure ℝ) [IsProbabilityMeasure ν] (a : ℝ)
    (hν : ν (Set.Icc a (a + 1))ᶜ = 0) :
    ∫ x, (∫ y, (x - y) ^ 2 ∂ν) ^ 2 ∂ν ≤ (1 / 2) * ∫ x, ∫ y, (x - y) ^ 2 ∂ν ∂ν := by sorry

end EmpiricalBernstein.SVP
