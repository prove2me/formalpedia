-- Prove2me | Theorems.Thm_APSCounting893_Main_rational_incidence_relation_bounded
-- name    : APSCounting893.Main.rational_incidence_relation_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:23:12.322859+00:00
-- url     : https://prove2.me/theorems/510ff611-f8a2-47ac-ab84-829c688339f7
-- title:
--   Degree-bounded incidence relation for a generically finite rational parametrization
-- statement:
--   Let $K$ be a field of characteristic zero and let $v_1,\ldots,v_m\in K(x_1,\ldots,x_r)$ be rational functions with a common nonzero denominator $Q$. Write $v_i=P_i/Q$ and assume that $Q$ and every $P_i$ have degree at most $d$, where $d\ge1$. Suppose that some $r$ of the $v_i$ are algebraically independent over $K$.
--
--   There is a nonzero polynomial $q$ in $(r+1)(m+1)$ matrix coefficients such that
--
--   $$\deg q\le(r+1)d^r$$
--
--   and $q$ vanishes identically on the generic matrices whose free entries are $B_{ij}$ and whose pivot entries satisfy
--
--   $$A_{i0}=-\sum_{j=1}^m B_{ij}v_j,\qquad A_{ij}=B_{ij}\quad(j>0).$$
--
--   This is a degree-bounded equation for the incidence locus of the projective closure of the rationally parametrized image. It supplies the quantitative output-projection certificate used in Proposition 3.14 of the APS argument.
--
--   **Formalization Note** The identity is evaluated in the fraction field of the polynomial ring in the independent free coefficients. Thus it is a polynomial identity, not an assumption about sampled coefficients.
-- source:
--   Jeronimo, Krick, Sabia and Sombra, The computational complexity of the Chow form, arXiv:math/0210009, Section 1.1, pp.6–7 (incidence equation and multidegree); applied to the projective image of [Q:P_1:...:P_m]. Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Proposition 3.14, pp.14–15. https://arxiv.org/pdf/math/0210009#page=6 ; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Mathlib
set_option autoImplicit false
open MvPolynomial

theorem APSCounting893.Main.rational_incidence_relation_bounded {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) K,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*d^r ∧ (let E := FractionRing (MvPolynomial (Fin r) K)
       let S := MvPolynomial (Fin (r+1) × Fin m) E
       MvPolynomial.aeval (R := K) (S₁ := FractionRing S) (fun a : Fin (r+1) × Fin (m+1) =>
         Fin.cases (-algebraMap S (FractionRing S) (∑ j : Fin m, MvPolynomial.X (a.1,j)*MvPolynomial.C (v j)))
           (fun j => algebraMap S (FractionRing S) (MvPolynomial.X (a.1,j))) a.2) q = 0) := by sorry
