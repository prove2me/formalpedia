-- Prove2me | Theorems.Thm_DerandLDT_lemma_3_17
-- name    : DerandLDT.lemma_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:13.436667+00:00
-- url     : https://prove2.me/theorems/f60d3f1b-c157-4057-83fd-bfd965b15601
-- title:
--   Lemma 3.17 — the Polishchuk–Spielman lemma [PS94] (corrected: $A \ne 0$)
-- statement:
--   There are constants $c > c' > 0$ such that the following holds for every field $\mathbb F$. Let $A(X, Y), B(X, Y) \in \mathbb F[X, Y]$ have $X$-degree and $Y$-degree at most $D$, with $A \neq 0$. Let $S_x \subseteq \mathbb F$ be a set of $n$ values $x$ such that $B(x, Y) = C_x(Y)\, A(x, Y)$ with $\deg C_x \le k$, and $S_y \subseteq \mathbb F$ a set of $n$ values $y$ such that $B(X, y) = R_y(X)\, A(X, y)$ with $\deg R_y \le k$. If $n > cD$, then there is $Q(X, Y)$ of degree at most $k$ in each variable with
--   $$
--   B(X, Y) = Q(X, Y) \cdot A(X, Y),
--   $$
--   and $Q(x, Y) = C_x(Y)$ and $Q(X, y) = R_y(X)$ for all but at most $c'D$ of the substitutions $x \in S_x$, $y \in S_y$.
--
--   The proof of Theorem 1.2 applies it to the numerator and denominator of the rational root found by Lemma 2.1 to show that the root is a polynomial of degree at most $2k$ (up to a $p$-th power).
--
--   **Formalization Note** $X, Y$ are the variables $0, 1$ of `MvPolynomial (Fin 2) F`; $B(x, Y)$ is the substitution $X = x$ as a univariate in $Y$. The quotients are given families $C_x$, $R_y$.
--
--   Differences from the source:
--   - correction: A(X, Y) any polynomial → A ≠ 0; reason: with A = B = 0, D = 0, k = 0 and two values x with quotients C_x = 0 and C_x = 1, every printed hypothesis holds but no Q of degree 0 matches both, against c′·0 = 0 exceptions
--   - reading: "for all but c′D choices of the substitutions x, y" → the number of exceptional x in S_x plus exceptional y in S_y is at most c′D; reason: the total over both families; a per-family bound follows
--   - encoding: A(x, Y) divides B(x, Y) and the quotient C_x(Y) has degree at most k → a given family C_x with B(x, Y) = C_x(Y)·A(x, Y) and deg C_x ≤ k (likewise R_y); reason: the quotient is unique when A(x, Y) ≠ 0; when A(x, Y) = 0 the hypothesis allows any C_x, and A ≠ 0 vanishes on at most D such lines
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 3.17, p.14

import Mathlib

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

open Classical in
/-- **Lemma 3.17** (Polishchuk–Spielman [PS94]), corrected with `A ≠ 0`. Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 3.17,
p.14: *Let `F` be any field and `A(X, Y), B(X, Y) ∈ F[X, Y]` have `X`- and `Y`-degrees at most
`D`. Let there be `n` values `x ∈ F` such that `A(x, Y)` divides `B(x, Y)` in `F[Y]` with quotient
`C_x(Y)` of degree at most `k`, and `n` values `y ∈ F` such that `A(X, y)` divides `B(X, y)` in
`F[X]` with quotient `R_y(X)` of degree at most `k`. There are constants `c > c′ > 0` such that if
`n > cD`, then there is `Q(X, Y)` of degree at most `k` in each variable with `B = Q·A`.
Furthermore, for all but `c′D` choices of the substitutions `x, y`, `Q(x, Y) = C_x(Y)` and
`Q(X, y) = R_y(X)`.*

**Formalization Note.** The hypothesis `A ≠ 0` corrects the printed statement: with
`A = B = 0`, `D = 0`, `k = 0` and two values `x` with quotients `C_x = 0` and `C_x = 1`, every
hypothesis holds, but no constant `Q` matches both, against `c′·0 = 0` exceptions. `X, Y` are
the variables `0, 1` of `MvPolynomial (Fin 2) F`; `B(x, Y)` is `aeval ![C x, X] B` and `B(X, y)`
is `aeval ![X, C y] B`. The quotients are given families `C_x`, `R_y` (when `A(x, Y) = 0` any
`C_x` satisfies the hypothesis). "All but `c′D` choices of the substitutions `x, y`" bounds the
total number of exceptional `x` and `y`. The constants are absolute (uniform in `F`). -/
theorem lemma_3_17 :
    ∃ c c' : ℝ, 0 < c' ∧ c' < c ∧ ∀ (F : Type u) [Field F] (D k n : ℕ)
      (A B : MvPolynomial (Fin 2) F), A ≠ 0 →
      A.degreeOf 0 ≤ D → A.degreeOf 1 ≤ D → B.degreeOf 0 ≤ D → B.degreeOf 1 ≤ D →
      ∀ (Sx Sy : Finset F) (Cx Ry : F → F[X]), Sx.card = n → Sy.card = n →
        (∀ x ∈ Sx, (Cx x).natDegree ≤ k ∧
          MvPolynomial.aeval ![C x, X] B = Cx x * MvPolynomial.aeval ![C x, X] A) →
        (∀ y ∈ Sy, (Ry y).natDegree ≤ k ∧
          MvPolynomial.aeval ![X, C y] B = Ry y * MvPolynomial.aeval ![X, C y] A) →
        c * (D : ℝ) < (n : ℝ) →
        ∃ Q : MvPolynomial (Fin 2) F, Q.degreeOf 0 ≤ k ∧ Q.degreeOf 1 ≤ k ∧ B = Q * A ∧
          (((Sx.filter fun x => MvPolynomial.aeval ![C x, X] Q ≠ Cx x).card +
              (Sy.filter fun y => MvPolynomial.aeval ![X, C y] Q ≠ Ry y).card : ℕ) : ℝ) ≤
            c' * (D : ℝ) := by sorry

end DerandLDT
