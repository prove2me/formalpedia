-- Prove2me | Theorems.Thm_APSCounting893_Main_jacobian_independence_criterion
-- name    : APSCounting893.Main.jacobian_independence_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:32:50.300438+00:00
-- url     : https://prove2.me/theorems/ba757a71-7086-40d8-9700-773ed08ab26c
-- title:
--   Jacobian criterion for algebraic independence in characteristic zero
-- statement:
--   Let $K$ be a field of characteristic zero, and let $f_1,\ldots,f_r\in K[x_1,\ldots,x_n]$. The polynomials are algebraically independent over $K$ if and only if their Jacobian has a nonzero $r\times r$ minor:
--
--   $$\{f_1,\ldots,f_r\}\text{ is algebraically independent}\quad\Longleftrightarrow\quad\exists J\subseteq\{1,\ldots,n\},\ |J|=r,\
--   \det\left(\frac{\partial f_i}{\partial x_j}\right)_{1\le i\le r,\,j\in J}\ne0.$$
--
--   The determinant is a polynomial, so nonvanishing here means it is not identically zero. This criterion relates algebraic image dimension to polynomial rank certificates and is used in the source's dimension computation and input-reduction argument. It includes the empty family with its empty determinant equal to one.
--
--   **Formalization Note** An injective function selects and orders the columns of the minor. Polynomial inputs may be arbitrary; no degree or polynomial-size representation assumption is imposed in this algebraic lemma.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Lemma 6.1 and its proof, p.23, especially the identification of transcendence degree with Jacobian rank preceding equation (6.1), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. The same characteristic-zero criterion applies to each coordinate subfamily.

import Mathlib
set_option autoImplicit false

theorem APSCounting893.Main.jacobian_independence_criterion
    {K : Type} [Field K] [CharZero K] {n r : ℕ}
    (F : Fin r → MvPolynomial (Fin n) K) :
    AlgebraicIndependent K F ↔
      ∃ g : Fin r → Fin n, Function.Injective g ∧
        (Matrix.of (fun i j => MvPolynomial.pderiv (g j) (F i))).det ≠ 0 := by sorry
