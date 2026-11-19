-- Prove2me | Theorems.Thm_APSCounting893_Main_perron_exceptional_polynomial
-- name    : APSCounting893.Main.perron_exceptional_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:34:15.982248+00:00
-- url     : https://prove2.me/theorems/2b29b28d-0627-4acb-b1b4-a3be665ca4fc
-- title:
--   Perron relations and the exceptional-locus degree bound
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^{n+1}$ be a reduced map of degree at most $d$, and let $\pi:Y\to\mathbb C^n$ be the prescribed linear Noether normalization of its image closure $Y$. There are univariate polynomials $Q_i(u,T)$ of positive $T$-degree, with nonzero leading coefficients $a_i(u)$, such that
--
--   $$Q_i(\pi(F(x)),x_i)=0,\qquad b(u)=\prod_{i=1}^n a_i(u)\ne0,\qquad \deg b\le nd^n.$$
--
--   For this same coefficient product, the exceptional set satisfies
--
--   $$\deg\{y\in Y:b(\pi(y))=0\}\le nd^{2n}.$$
--
--   Degree is the projective degree of the actual filtered coordinate ring. These relations and their common exceptional polynomial are the algebraic data used in Proposition 4.1.
-- source:
--   Agarwal, Hari, Pandey, Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 4.1, p. 16, Perron relations and proof of Proposition 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_LineGeometry

set_option autoImplicit false
open APSCounting893.Main MvPolynomial

theorem APSCounting893.Main.perron_exceptional_polynomial (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    ∃ (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n),
      b = ∏ i, (p i).leadingCoeff ∧ b ≠ 0 ∧ b.totalDegree ≤ F.n * F.d ^ F.n ∧
      (∀ i, 0 < (p i).natDegree) ∧
      (∀ i x, Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) ∧
      projectiveDegree {y ∈ imageClosure F.F | eval (normalization c y) b = 0} ≤
        F.n * F.d ^ (2 * F.n) := by sorry
