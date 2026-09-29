-- Prove2me | Theorems.Thm_Diaz_indep_three
-- name    : Diaz.indep_three
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:02.687757+00:00
-- url     : https://prove2.me/theorems/f324af6b-829b-4459-940c-285e051fcdce
-- title:
--   $1$, $u$ and $\bar u$ are linearly independent over the base field
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $u \in \mathbb{C}$ transcendental over $K$ with $\rho := u\bar u \in K$. If $a, b, c \in K$ satisfy
--
--   $$a + b\,u + c\,\bar u = 0,$$
--
--   then $a = b = c = 0$.
--
--   **Why.** Substituting $\bar u = \rho/u$ and clearing the denominator turns the relation into $b\,u^{2} + a\,u + c\rho = 0$, a quadratic over $K$. If any of $a,b,c$ were non-zero, that polynomial would be non-zero — its coefficients are $b$, $a$ and $c\rho$, and $\rho \neq 0$ — so $u$ would be algebraic over $K$, contrary to hypothesis.
--
--   **Role.** This is one of the two clauses of the stability lemma of the accompanying note; the other, conjugation-stability of the hull, is `Diaz.conj_mem_hull`. Together they say that the span $W_u$ of $\{1, u, \bar u\}$ over $K$ is a three-dimensional conjugation-stable space, which is the setting in which the rank and coefficient statements about the matrix $H$ are formulated.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Nodes.lean#L65-L101

import Mathlib

open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

theorem Diaz.indep_three (hT : Transcendental K u) (hρ : u * conj u ∈ K)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (h : a + b * u + c * conj u = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by sorry
