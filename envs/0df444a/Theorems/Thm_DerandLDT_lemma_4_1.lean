-- Prove2me | Theorems.Thm_DerandLDT_lemma_4_1
-- name    : DerandLDT.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:00.042518+00:00
-- url     : https://prove2.me/theorems/ef9f0056-5bf1-4e7f-b4fc-6bb5788dc1fe
-- title:
--   Lemma 4.1 — lifting consistent roots on axis-parallel lines to a root $U \in \mathbb F(X)[Y]$
-- statement:
--   Let $\mathbb F$ be a field and $Q(X, Y, Z) \in \mathbb F[X, Y, Z]$ a nonzero polynomial of $(1, 1, k)$-degree at most $D$ (every monomial $X^iY^jZ^\ell$ of $Q$ has $i + j + k\ell \le D$), and let $d_Z(Q)$ be its $Z$-degree. Let $S \subseteq \mathbb F$ be finite and, for every $a \in S$, let $g_a(Y)$ have degree at most $k$ with $Q(a, Y, g_a(Y)) \equiv 0$. Let $h(X)$ have degree at most $k$ with
--
--   1. $Q(X, 0, h(X)) \equiv 0$,
--   2. $(\partial_Z Q)(X, 0, h(X)) \not\equiv 0$,
--   3. $h(a) = g_a(0)$ for every $a \in S$.
--
--   If $|S| > 2D + d_Z(Q)\, D\, (2k + 1)$, then there is $U(X, Y) \in \mathbb F(X)[Y]$ with $\deg_Y U \le k$, $\deg_X U \le Dk$ and
--   $$
--   Q(X, Y, U(X, Y)) \equiv 0 .
--   $$
--   Moreover, for all but at most $D$ values $a \in S$, $U(a, Y)$ is well defined and equals $g_a(Y)$.
--
--   This is the axis-parallel case of Lemma 2.1: a root on an anchor line, consistent with roots on many parallel lines, lifts to a global rational root.
--
--   **Formalization Note** $U$ is written over a common denominator as $N(X, Y)/M(X)$ with $M \neq 0$, $\deg_Y N \le k$ and $\deg_X N, \deg M \le Dk$; the identity $Q(X, Y, N/M) = 0$ holds in the fraction field of $\mathbb F[X, Y]$, and "$U(a, Y)$ is well defined and equals $g_a$" is $M(a) \neq 0$ and $N(a, Y) = M(a)\, g_a(Y)$.
--
--   Differences from the source:
--   - reading: "∂_Z(Q(X, 0, h(X))) is non-zero" → (∂_Z Q)(X, 0, h(X)) ≠ 0, the Z-derivative of Q with (X, 0, h(X)) substituted; reason: the univariate Q(X, 0, h(X)) has no Z; Claim 4.2 uses ∂_Z(Q)(a, 0, h(a)) ≠ 0, as Lemma 2.1 states
--   - generalization: Q of (1, 1, k)-degree D; h a degree k polynomial → (1, 1, k)-degree at most D; deg h ≤ k; reason: the exact-degree cases are instances; D is used only as an upper bound in the proof
--   - generalization: U ∈ F(X)[Y] with deg_X(U) ≤ Dk → U = N/M with N ∈ F[X, Y], 0 ≠ M ∈ F[X], deg_Y N ≤ k, deg_X N ≤ Dk, deg M ≤ Dk, root identity in the fraction field of F[X, Y]; reason: a single common denominator of degree ≤ Dk is stronger than each coefficient of U having degree ≤ Dk (p.10), so the Lean conclusion implies the printed one; it is still true because the lowest-terms root N/M gives a factor MZ − N of Q (Gauss), whose (1, 1, k)-degree is at most D
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 4.1, p.16

import Mathlib

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

open Classical in
/-- **Lemma 4.1** (lifting from consistent axis-parallel lines). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 4.1, p.16: *Let
`Q(X, Y, Z)` be a nonzero trivariate polynomial of `(1, 1, k)`-degree `D`. Let `S ⊆ F` be such that
for every `a ∈ S` some `g_a(Y)` of degree at most `k` satisfies `Q(a, Y, g_a(Y)) ≡ 0`. Let `h(X)`
be a degree `k` polynomial such that `Q(X, 0, h(X))` is identically zero, `∂_Z(Q(X, 0, h(X)))` is
nonzero, and `h(a) = g_a(0)` for every `a ∈ S`. If `|S| > 2D + d_Z(Q)·D(2k + 1)`, then there is
`U(X, Y) ∈ F(X)[Y]` with `deg_Y(U) ≤ k`, `deg_X(U) ≤ Dk` and `Q(X, Y, U(X, Y)) ≡ 0`. Moreover,
for all but at most `D` choices of `a ∈ S`, `U(a, Y) = g_a(Y)`.*

**Formalization Note.** `X, Y, Z` are the variables `0, 1, 2` of `MvPolynomial (Fin 3) F`; the
`(1, 1, k)`-degree is `weightedTotalDegree ![1, 1, k]`, and "of `(1, 1, k)`-degree `D`" is read
as "at most `D`". `d_Z(Q)` is `degreeOf 2 Q`. Restrictions are formal univariate polynomials:
`Q(a, Y, g_a(Y))` is `aeval ![C a, X, g_a] Q` and `Q(X, 0, h(X))` is `aeval ![X, 0, h] Q`.
"`∂_Z(Q(X, 0, h(X)))` is nonzero" is read as `(∂_Z Q)(X, 0, h(X)) ≠ 0` (the `Z`-derivative of
`Q` substituted), as in Claim 4.2 and Lemma 2.1. `h` and the `g_a` have degree at most `k`.
`U ∈ F(X)[Y]` is written over a common denominator, `U = N(X, Y)/M(X)` with `M ≠ 0`,
`deg_Y N ≤ k` and `deg_X N, deg M ≤ Dk`, and `Q(X, Y, N/M) = 0` holds in the fraction field
of `F[X, Y]`. "`U(a, Y)` is well defined and equals `g_a(Y)`" is
`M(a) ≠ 0 ∧ N(a, Y) = M(a)·g_a(Y)`. `F` is any field. -/
theorem lemma_4_1 (F : Type u) [Field F] (k D : ℕ) (Q : MvPolynomial (Fin 3) F) (hQ : Q ≠ 0)
    (hD : MvPolynomial.weightedTotalDegree ![1, 1, k] Q ≤ D)
    (S : Finset F) (g : F → F[X])
    (hg : ∀ a ∈ S, (g a).natDegree ≤ k ∧ MvPolynomial.aeval ![C a, X, g a] Q = 0)
    (h : F[X]) (hh : h.natDegree ≤ k) (hQh : MvPolynomial.aeval ![X, 0, h] Q = 0)
    (hQh' : MvPolynomial.aeval ![X, 0, h] (MvPolynomial.pderiv 2 Q) ≠ 0)
    (hgh : ∀ a ∈ S, h.eval a = (g a).eval 0)
    (hS : 2 * D + Q.degreeOf 2 * D * (2 * k + 1) < S.card) :
    ∃ (N : MvPolynomial (Fin 2) F) (M : F[X]), M ≠ 0 ∧
      N.degreeOf 1 ≤ k ∧ N.degreeOf 0 ≤ D * k ∧ M.natDegree ≤ D * k ∧
      MvPolynomial.eval₂
          ((algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F))).comp
            MvPolynomial.C)
          ![algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) (MvPolynomial.X 0),
            algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) (MvPolynomial.X 1),
            algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) N /
              algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F))
                (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) F) M)] Q = 0 ∧
      (S.filter fun a =>
          ¬ (M.eval a ≠ 0 ∧ MvPolynomial.aeval ![C a, X] N = C (M.eval a) * g a)).card ≤ D := by sorry

end DerandLDT
