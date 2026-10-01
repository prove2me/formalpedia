-- Prove2me | Theorems.Thm_AlbouyKaloshin_lemma1_image_finite_or_cofinite
-- name    : AlbouyKaloshin.lemma1_image_finite_or_cofinite
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T20:54:00.628725+00:00
-- url     : https://prove2.me/theorems/47ee5575-96c5-4bb6-8302-754d71e2e216
-- title:
--   Lemma 1: a polynomial image of an affine variety is finite or cofinite
-- statement:
--   Let $N\ge 0$, let $S$ be a set of complex polynomials in $N$ variables, and let $X=\{z\in\mathbb C^N : p(z)=0 \text{ for all } p\in S\}$ be the closed algebraic subset it defines. For every polynomial $f\in\mathbb C[z_1,\dots,z_N]$,
--   $$
--   f(X)\ \text{is finite}\qquad\text{or}\qquad \mathbb C\setminus f(X)\ \text{is finite}.
--   $$
--   In the second case $f$ is called *dominating* on $X$. This is the only fact from elimination theory used in the paper to pass from infinitely many solutions to unbounded (singular) sequences of solutions.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 540, Lemma 1

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem lemma1_image_finite_or_cofinite (N : ℕ) (S : Set (MvPolynomial (Fin N) ℂ))
    (f : MvPolynomial (Fin N) ℂ) :
    ((fun z => MvPolynomial.eval z f) '' {z : Fin N → ℂ | ∀ p ∈ S, MvPolynomial.eval z p = 0}).Finite ∨
    ((fun z => MvPolynomial.eval z f) '' {z : Fin N → ℂ | ∀ p ∈ S, MvPolynomial.eval z p = 0})ᶜ.Finite := by sorry

end AlbouyKaloshin
