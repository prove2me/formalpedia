-- Prove2me | Theorems.Thm_APSCounting893_Main_perron_nonvanishing_finite_surjective
-- name    : APSCounting893.Main.perron_nonvanishing_finite_surjective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:34:26.028715+00:00
-- url     : https://prove2.me/theorems/4102dce2-8d46-479d-bc53-b592d21277d6
-- title:
--   Finite surjective coverage off the Perron coefficient product
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^{n+1}$ be a reduced map, let $Y$ be its image closure, and let $\pi:Y\to\mathbb C^n$ be its prescribed linear Noether normalization. Suppose polynomials $Q_i(u,T)$ satisfy $Q_i(\pi(F(x)),x_i)=0$ for every $x$, and their leading coefficients have nonzero product $b(u)$. Then
--
--   $$U=\{y\in Y:b(\pi(y))\ne0\}$$
--
--   is a nonempty relatively open subset of $Y$, every point of $U$ lies in the actual image of $F$, and the map from the input affine space is finite over $U$.
--
--   Finiteness is expressed by fixed polynomial generators whose coefficients on this open set are polynomial functions of the outputs divided by powers of one nonvanishing polynomial. This is the finite-surjective step in the proof of Proposition 4.1.
-- source:
--   Agarwal, Hari, Pandey, Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 4.1, p. 16, Perron relations and proof of Proposition 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_LineGeometry

set_option autoImplicit false
open APSCounting893.Main MvPolynomial

theorem APSCounting893.Main.perron_nonvanishing_finite_surjective (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c)
    (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n)
    (hb : b ≠ 0) (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine ℂ F.n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) :
    GoodOpen F {y ∈ imageClosure F.F | eval (normalization c y) b ≠ 0} := by sorry
